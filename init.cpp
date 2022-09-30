/*
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "init.h"

#include <dirent.h>
#include <fcntl.h>
#include <paths.h>
#include <pthread.h>
#include <seccomp_policy.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/mount.h>
#include <sys/signalfd.h>
#include <sys/sysmacros.h>
#include <sys/types.h>
#include <unistd.h>

#include <android-base/chrono_utils.h>
#include <android-base/file.h>
#include <android-base/logging.h>
#include <android-base/properties.h>
#include <android-base/stringprintf.h>
#include <android-base/strings.h>
#include <cutils/android_reboot.h>
#include <keyutils.h>
#include <libavb/libavb.h>
#include <private/android_filesystem_config.h>
#include <selinux/android.h>

#include <memory>
#include <optional>

#include "action_parser.h"
#include "import_parser.h"
#include "init_first_stage.h"
#include "keychords.h"
#include "log.h"
#include "property_service.h"
#include "reboot.h"
#include "security.h"
#include "selinux.h"
#include "sigchld_handler.h"
#include "ueventd.h"
#include "util.h"
#include "watchdogd.h"

using namespace std::string_literals;

using android::base::boot_clock;
using android::base::GetProperty;
using android::base::ReadFileToString;
using android::base::StringPrintf;
using android::base::Timer;
using android::base::Trim;

namespace android {
namespace init {

static int property_triggers_enabled = 0;

static char qemu[32];

std::string default_console = "/dev/console";

static int epoll_fd = -1;
static int sigterm_signal_fd = -1;

static std::unique_ptr<Timer> waiting_for_prop(nullptr);
static std::string wait_prop_name;
static std::string wait_prop_value;
static bool shutting_down;
static std::string shutdown_command;
static bool do_shutdown = false;

std::vector<std::string> late_import_paths;

static std::vector<Subcontext>* subcontexts;

void DumpState() {
    ServiceList::GetInstance().DumpState();
    ActionManager::GetInstance().DumpState();
}

Parser CreateParser(ActionManager& action_manager, ServiceList& service_list) {
    Parser parser;

    parser.AddSectionParser("service", std::make_unique<ServiceParser>(&service_list, subcontexts));
    parser.AddSectionParser("on", std::make_unique<ActionParser>(&action_manager, subcontexts));
    parser.AddSectionParser("import", std::make_unique<ImportParser>(&parser));

    return parser;
}

static void LoadBootScripts(ActionManager& action_manager, ServiceList& service_list) {
    Parser parser = CreateParser(action_manager, service_list);

    std::string bootscript = GetProperty("ro.boot.init_rc", "");
    if (bootscript.empty()) {
        parser.ParseConfig("/init.rc");
        if (!parser.ParseConfig("/system/etc/init")) {
            late_import_paths.emplace_back("/system/etc/init");
        }
        if (!parser.ParseConfig("/product/etc/init")) {
            late_import_paths.emplace_back("/product/etc/init");
        }
        if (!parser.ParseConfig("/odm/etc/init")) {
            late_import_paths.emplace_back("/odm/etc/init");
        }
        if (!parser.ParseConfig("/vendor/etc/init")) {
            late_import_paths.emplace_back("/vendor/etc/init");
        }
    } else {
        parser.ParseConfig(bootscript);
    }
}

void register_epoll_handler(int fd, void (*fn)()) {
    epoll_event ev;
    ev.events = EPOLLIN;
    ev.data.ptr = reinterpret_cast<void*>(fn);
    if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, fd, &ev) == -1) {
        PLOG(ERROR) << "epoll_ctl failed";
    }
}

bool start_waiting_for_property(const char *name, const char *value)
{
    if (waiting_for_prop) {
        return false;
    }
    if (GetProperty(name, "") != value) {
        // Current property value is not equal to expected value
        wait_prop_name = name;
        wait_prop_value = value;
        waiting_for_prop.reset(new Timer());
    } else {
        LOG(INFO) << "start_waiting_for_property(\""
                  << name << "\", \"" << value << "\"): already set";
    }
    return true;
}

void ResetWaitForProp() {
    wait_prop_name.clear();
    wait_prop_value.clear();
    waiting_for_prop.reset();
}

void property_changed(const std::string& name, const std::string& value) {
    // If the property is sys.powerctl, we bypass the event queue and immediately handle it.
    // This is to ensure that init will always and immediately shutdown/reboot, regardless of
    // if there are other pending events to process or if init is waiting on an exec service or
    // waiting on a property.
    // In non-thermal-shutdown case, 'shutdown' trigger will be fired to let device specific
    // commands to be executed.
    if (name == "sys.powerctl") {
        // Despite the above comment, we can't call HandlePowerctlMessage() in this function,
        // because it modifies the contents of the action queue, which can cause the action queue
        // to get into a bad state if this function is called from a command being executed by the
        // action queue.  Instead we set this flag and ensure that shutdown happens before the next
        // command is run in the main init loop.
        // TODO: once property service is removed from init, this will never happen from a builtin,
        // but rather from a callback from the property service socket, in which case this hack can
        // go away.
        shutdown_command = value;
        do_shutdown = true;
    }

    if (property_triggers_enabled) ActionManager::GetInstance().QueuePropertyChange(name, value);

    if (waiting_for_prop) {
        if (wait_prop_name == name && wait_prop_value == value) {
            LOG(INFO) << "Wait for property took " << *waiting_for_prop;
            ResetWaitForProp();
        }
    }
}

static std::optional<boot_clock::time_point> RestartProcesses() {
    std::optional<boot_clock::time_point> next_process_restart_time;
    for (const auto& s : ServiceList::GetInstance()) {
        if (!(s->flags() & SVC_RESTARTING)) continue;

        auto restart_time = s->time_started() + 5s;
        if (boot_clock::now() > restart_time) {
            if (auto result = s->Start(); !result) {
                LOG(ERROR) << "Could not restart process '" << s->name() << "': " << result.error();
            }
        } else {
            if (!next_process_restart_time || restart_time < *next_process_restart_time) {
                next_process_restart_time = restart_time;
            }
        }
    }
    return next_process_restart_time;
}

static Result<Success> DoControlStart(Service* service) {
    return service->Start();
}

static Result<Success> DoControlStop(Service* service) {
    service->Stop();
    return Success();
}

static Result<Success> DoControlRestart(Service* service) {
    service->Restart();
    return Success();
}

enum class ControlTarget {
    SERVICE,    // function gets called for the named service
    INTERFACE,  // action gets called for every service that holds this interface
};

struct ControlMessageFunction {
    ControlTarget target;
    std::function<Result<Success>(Service*)> action;
};

static const std::map<std::string, ControlMessageFunction>& get_control_message_map() {
    // clang-format off
    static const std::map<std::string, ControlMessageFunction> control_message_functions = {
        {"start",             {ControlTarget::SERVICE,   DoControlStart}},
        {"stop",              {ControlTarget::SERVICE,   DoControlStop}},
        {"restart",           {ControlTarget::SERVICE,   DoControlRestart}},
        {"interface_start",   {ControlTarget::INTERFACE, DoControlStart}},
        {"interface_stop",    {ControlTarget::INTERFACE, DoControlStop}},
        {"interface_restart", {ControlTarget::INTERFACE, DoControlRestart}},
    };
    // clang-format on

    return control_message_functions;
}

void HandleControlMessage(const std::string& msg, const std::string& name, pid_t pid) {
    const auto& map = get_control_message_map();
    const auto it = map.find(msg);

    if (it == map.end()) {
        LOG(ERROR) << "Unknown control msg '" << msg << "'";
        return;
    }

    std::string cmdline_path = StringPrintf("proc/%d/cmdline", pid);
    std::string process_cmdline;
    if (ReadFileToString(cmdline_path, &process_cmdline)) {
        std::replace(process_cmdline.begin(), process_cmdline.end(), '\0', ' ');
        process_cmdline = Trim(process_cmdline);
    } else {
        process_cmdline = "unknown process";
    }

    LOG(INFO) << "Received control message '" << msg << "' for '" << name << "' from pid: " << pid
              << " (" << process_cmdline << ")";

    const ControlMessageFunction& function = it->second;

    if (function.target == ControlTarget::SERVICE) {
        Service* svc = ServiceList::GetInstance().FindService(name);
        if (svc == nullptr) {
            LOG(ERROR) << "No such service '" << name << "' for ctl." << msg;
            return;
        }
        if (auto result = function.action(svc); !result) {
            LOG(ERROR) << "Could not ctl." << msg << " for service " << name << ": "
                       << result.error();
        }

        return;
    }

    if (function.target == ControlTarget::INTERFACE) {
        for (const auto& svc : ServiceList::GetInstance()) {
            if (svc->interfaces().count(name) == 0) {
                continue;
            }

            if (auto result = function.action(svc.get()); !result) {
                LOG(ERROR) << "Could not handle ctl." << msg << " for service " << svc->name()
                           << " with interface " << name << ": " << result.error();
            }

            return;
        }

        LOG(ERROR) << "Could not find service hosting interface " << name;
        return;
    }

    LOG(ERROR) << "Invalid function target from static map key '" << msg
               << "': " << static_cast<std::underlying_type<ControlTarget>::type>(function.target);
}

static Result<Success> wait_for_coldboot_done_action(const BuiltinArguments& args) {
    Timer t;

    LOG(VERBOSE) << "Waiting for " COLDBOOT_DONE "...";

    // Historically we had a 1s timeout here because we weren't otherwise
    // tracking boot time, and many OEMs made their sepolicy regular
    // expressions too expensive (http://b/19899875).

    // Now we're tracking boot time, just log the time taken to a system
    // property. We still panic if it takes more than a minute though,
    // because any build that slow isn't likely to boot at all, and we'd
    // rather any test lab devices fail back to the bootloader.
    if (wait_for_file(COLDBOOT_DONE, 60s) < 0) {
        LOG(FATAL) << "Timed out waiting for " COLDBOOT_DONE;
    }

    property_set("ro.boottime.init.cold_boot_wait", std::to_string(t.duration().count()));
    return Success();
}

static Result<Success> keychord_init_action(const BuiltinArguments& args) {
    keychord_init();
    return Success();
}

static Result<Success> console_init_action(const BuiltinArguments& args) {
    std::string console = GetProperty("ro.boot.console", "");
    if (!console.empty()) {
        default_console = "/dev/" + console;
    }
    return Success();
}

static void import_kernel_nv(const std::string& key, const std::string& value, bool for_emulator) {
    if (key.empty()) return;

    if (for_emulator) {
        // In the emulator, export any kernel option with the "ro.kernel." prefix.
        property_set("ro.kernel." + key, value);
        return;
    }

    if (key == "qemu") {
        strlcpy(qemu, value.c_str(), sizeof(qemu));
    } else if (android::base::StartsWith(key, "androidboot.")) {
        property_set("ro.boot." + key.substr(12), value);
    }
}

static void export_oem_lock_status() {
    if (!android::base::GetBoolProperty("ro.oem_unlock_supported", false)) {
        return;
    }

    std::string value = GetProperty("ro.boot.verifiedbootstate", "");

    if (!value.empty()) {
        property_set("ro.boot.flash.locked", value == "orange" ? "0" : "1");
    }
}

static void export_kernel_boot_props() {
    struct {
        const char *src_prop;
        const char *dst_prop;
        const char *default_value;
    } prop_map[] = {
        { "ro.boot.serialno",   "ro.serialno",   "", },
        { "ro.boot.mode",       "ro.bootmode",   "unknown", },
        { "ro.boot.baseband",   "ro.baseband",   "unknown", },
        { "ro.boot.bootloader", "ro.bootloader", "unknown", },
        { "ro.boot.hardware",   "ro.hardware",   "unknown", },
        { "ro.boot.revision",   "ro.revision",   "0", },
    };
    for (size_t i = 0; i < arraysize(prop_map); i++) {
        std::string value = GetProperty(prop_map[i].src_prop, "");
        property_set(prop_map[i].dst_prop, (!value.empty()) ? value : prop_map[i].default_value);
    }
}

static void process_kernel_dt() {
    if (!is_android_dt_value_expected("compatible", "android,firmware")) {
        return;
    }

    std::unique_ptr<DIR, int (*)(DIR*)> dir(opendir(get_android_dt_dir().c_str()), closedir);
    if (!dir) return;

    std::string dt_file;
    struct dirent *dp;
    while ((dp = readdir(dir.get())) != NULL) {
        if (dp->d_type != DT_REG || !strcmp(dp->d_name, "compatible") || !strcmp(dp->d_name, "name")) {
            continue;
        }

        std::string file_name = get_android_dt_dir() + dp->d_name;

        android::base::ReadFileToString(file_name, &dt_file);
        std::replace(dt_file.begin(), dt_file.end(), ',', '.');

        property_set("ro.boot."s + dp->d_name, dt_file);
    }
}

static void process_kernel_cmdline() {
    // The first pass does the common stuff, and finds if we are in qemu.
    // The second pass is only necessary for qemu to export all kernel params
    // as properties.
    import_kernel_cmdline(false, import_kernel_nv);
    if (qemu[0]) import_kernel_cmdline(true, import_kernel_nv);
}

static Result<Success> property_enable_triggers_action(const BuiltinArguments& args) {
    /* Enable property triggers. */
    property_triggers_enabled = 1;
    return Success();
}

static Result<Success> queue_property_triggers_action(const BuiltinArguments& args) {
    ActionManager::GetInstance().QueueBuiltinAction(property_enable_triggers_action, "enable_property_trigger");
    ActionManager::GetInstance().QueueAllPropertyActions();
    return Success();
}

static void global_seccomp() {
    import_kernel_cmdline(false, [](const std::string& key, const std::string& value, bool in_qemu) {
        if (key == "androidboot.seccomp" && value == "global" && !set_global_seccomp_filter()) {
            LOG(FATAL) << "Failed to globally enable seccomp!";
        }
    });
}

// Set the UDC controller for the ConfigFS USB Gadgets.
// Read the UDC controller in use from "/sys/class/udc".
// In case of multiple UDC controllers select the first one.
static void set_usb_controller() {
    std::unique_ptr<DIR, decltype(&closedir)>dir(opendir("/sys/class/udc"), closedir);
    if (!dir) return;

    dirent* dp;
    while ((dp = readdir(dir.get())) != nullptr) {
        if (dp->d_name[0] == '.') continue;

        property_set("sys.usb.controller", dp->d_name);
        break;
    }
}

static void InstallRebootSignalHandlers() {
    // Instead of panic'ing the kernel as is the default behavior when init crashes,
    // we prefer to reboot to bootloader on development builds, as this will prevent
    // boot looping bad configurations and allow both developers and test farms to easily
    // recover.
    struct sigaction action;
    memset(&action, 0, sizeof(action));
    sigfillset(&action.sa_mask);
    action.sa_handler = [](int signal) {
        // These signal handlers are also caught for processes forked from init, however we do not
        // want them to trigger reboot, so we directly call _exit() for children processes here.
        if (getpid() != 1) {
            _exit(signal);
        }

        // Calling DoReboot() or LOG(FATAL) is not a good option as this is a signal handler.
        // RebootSystem uses syscall() which isn't actually async-signal-safe, but our only option
        // and probably good enough given this is already an error case and only enabled for
        // development builds.
        RebootSystem(ANDROID_RB_RESTART2, "bootloader");
    };
    action.sa_flags = SA_RESTART;
    sigaction(SIGABRT, &action, nullptr);
    sigaction(SIGBUS, &action, nullptr);
    sigaction(SIGFPE, &action, nullptr);
    sigaction(SIGILL, &action, nullptr);
    sigaction(SIGSEGV, &action, nullptr);
#if defined(SIGSTKFLT)
    sigaction(SIGSTKFLT, &action, nullptr);
#endif
    sigaction(SIGSYS, &action, nullptr);
    sigaction(SIGTRAP, &action, nullptr);
}

static void HandleSigtermSignal() {
    signalfd_siginfo siginfo;
    ssize_t bytes_read = TEMP_FAILURE_RETRY(read(sigterm_signal_fd, &siginfo, sizeof(siginfo)));
    if (bytes_read != sizeof(siginfo)) {
        PLOG(ERROR) << "Failed to read siginfo from sigterm_signal_fd";
        return;
    }

    if (siginfo.ssi_pid != 0) {
        // Drop any userspace SIGTERM requests.
        LOG(DEBUG) << "Ignoring SIGTERM from pid " << siginfo.ssi_pid;
        return;
    }

    HandlePowerctlMessage("shutdown,container");
}

static void UnblockSigterm() {
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGTERM);

    if (sigprocmask(SIG_UNBLOCK, &mask, nullptr) == -1) {
        PLOG(FATAL) << "failed to unblock SIGTERM for PID " << getpid();
    }
}

static void InstallSigtermHandler() {
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGTERM);

    if (sigprocmask(SIG_BLOCK, &mask, nullptr) == -1) {
        PLOG(FATAL) << "failed to block SIGTERM";
    }

    // Register a handler to unblock SIGTERM in the child processes.
    const int result = pthread_atfork(nullptr, nullptr, &UnblockSigterm);
    if (result != 0) {
        LOG(FATAL) << "Failed to register a fork handler: " << strerror(result);
    }

    sigterm_signal_fd = signalfd(-1, &mask, SFD_CLOEXEC);
    if (sigterm_signal_fd == -1) {
        PLOG(FATAL) << "failed to create signalfd for SIGTERM";
    }

    register_epoll_handler(sigterm_signal_fd, HandleSigtermSignal);
}

// 1.C++中主函数有两个参数，第一个参数argc表示参数个数，第二个参数是参数列表，也就是具体的参数
// 2.init的main函数有两个其它入口，一是参数中有ueventd，进入ueventd_main,二是参数中有watchdogd，进入watchdogd_main
int main(int argc, char** argv) {
    // 1.strcmp是String的一个函数，比较字符串，相等返回0。
    // 2.C++中：0为false，非0为true。
    // 3.basename是C库中的一个函数，得到特定的路径中的最后一个'/'后面的内容，比如/sdcard/miui_recovery/backup，得到的结果是backup
    if (!strcmp(basename(argv[0]), "ueventd")) {
        // 当argv[0]的内容为 ueventd 时，strcmp的值为0，等价于 false,!strcmp()为1，等价于 true
        // 因此，这里进入if语句，执行ueventd_main()函数，ueventd_main()函数 主要是负责设备节点的创建、权限设定等一系列工作
        return ueventd_main(argc, argv);
    }
    // watchdogd 俗称看门狗，用于系统出问题时重启系统，相当于守护进程。
    if (!strcmp(basename(argv[0]), "watchdogd")) {
        return watchdogd_main(argc, argv);
    }

    if (argc > 1 && !strcmp(argv[1], "subcontext")) {
        InitKernelLogging(argv);
        const BuiltinFunctionMap function_map;
        return SubcontextMain(argc, argv, &function_map);
    }

    if (REBOOT_BOOTLOADER_ON_PANIC) {
        InstallRebootSignalHandlers();
    }
    // 查看是否有环境变量INIT_SECOND_STAGE
    bool is_first_stage = (getenv("INIT_SECOND_STAGE") == nullptr);
    // Get the basic filesystem setup we need put together in the initramdisk
    // on / and then we'll let the rc file figure out the rest.
    // 启动的第一阶段：挂栽和创建必需的文件目录
    // 1.init的main方法会执行两次，由is_first_stage控制,first_stage就是第一阶段要做的事
    // 2.mount()是用来挂载文件系统的，mount属于Linux系统调用
    if (is_first_stage) {
        boot_clock::time_point start_time = boot_clock::now();

        // Clear the umask.
        umask(0);//清空文件权限

        clearenv();
        setenv("PATH", _PATH_DEFPATH, 1);
        // Get the basic filesystem setup we need put together in the initramdisk
        // on / and then we'll let the rc file figure out the rest.
        // mount：用来挂载文件系统的，mount属于Linux系统调用
        mount("tmpfs", "/dev", "tmpfs", MS_NOSUID, "mode=0755");
        // mkdir：创建目录，第一个参数是目录路径，第二个是读写权限
        mkdir("/dev/pts", 0755);
        mkdir("/dev/socket", 0755);
        mount("devpts", "/dev/pts", "devpts", 0, NULL);；
        #define MAKE_STR(x) __STRING(x)
        mount("proc", "/proc", "proc", 0, "hidepid=2,gid=" MAKE_STR(AID_READPROC));
        // Don't expose the raw commandline to unprivileged processes.
        chmod("/proc/cmdline", 0440);//用于修改文件/目录的读写权限
        gid_t groups[] = { AID_READPROC };
        setgroups(arraysize(groups), groups);// 用来将list 数组中所标明的组加入到目前进程的组设置中
        mount("sysfs", "/sys", "sysfs", 0, NULL);
        mount("selinuxfs", "/sys/fs/selinux", "selinuxfs", 0, NULL);// selinuxfs：Linux系统的安全机制
        //mknod：用于创建Linux中的设备文件
        mknod("/dev/kmsg", S_IFCHR | 0600, makedev(1, 11));

        if constexpr (WORLD_WRITABLE_KMSG) {
            mknod("/dev/kmsg_debug", S_IFCHR | 0622, makedev(1, 11));
        }

        mknod("/dev/random", S_IFCHR | 0666, makedev(1, 8));
        mknod("/dev/urandom", S_IFCHR | 0666, makedev(1, 9));

        // Mount staging areas for devices managed by vold
        // See storage config details at http://source.android.com/devices/storage/
        mount("tmpfs", "/mnt", "tmpfs", MS_NOEXEC | MS_NOSUID | MS_NODEV, "mode=0755,uid=0,gid=1000");
        // /mnt/vendor is used to mount vendor-specific partitions that can not be
        // part of the vendor partition, e.g. because they are mounted read-write.
        mkdir("/mnt/vendor", 0755);

        // Now that tmpfs is mounted on /dev and we have /dev/kmsg, we can actually talk to the outside world...
        // 系统启动的第二阶段，初始化Linux Kernel内核的日志系统
        //将标准输入输出重定向到"/sys/fs/selinux/null"
        InitKernelLogging(argv);

        LOG(INFO) << "init first stage started!";

        if (!DoFirstStageMount()) {
            LOG(FATAL) << "Failed to mount required partitions early ...";
        }
        // Avb即Android Verfied boot,功能包括Secure Boot, verfying boot 和 dm-verity,
        // 原理都是对二进制文件进行签名，在系统启动时进行认证，确保系统运行的是合法的二进制镜像文件。
        // 其中认证的范围涵盖：bootloader，boot.img，system.img
        SetInitAvbVersionInRecovery();

        // Enable seccomp if global boot option was passed (otherwise it is enabled in zygote).
        global_seccomp();

        // Set up SELinux, loading the SELinux policy.
        SelinuxSetupKernelLogging();
        SelinuxInitialize();//加载SELinux policy，也就是安全策略，

        // We're in the kernel domain, so re-exec init to transition to the init domain now that the SELinux policy has been loaded.
        // 1.这句英文大概意思是，我们执行第一遍时是在kernel domain，所以要重新执行init文件，切换到init domain，这样SELinux policy才已经加载进来了
        // 2.后面的security_failure函数会调用panic重启系统
        if (selinux_android_restorecon("/init", 0) == -1) {
            PLOG(FATAL) << "restorecon failed of /init failed";
        }

        setenv("INIT_SECOND_STAGE", "true", 1);

        static constexpr uint32_t kNanosecondsPerMillisecond = 1e6;
        uint64_t start_ms = start_time.time_since_epoch().count() / kNanosecondsPerMillisecond;
        setenv("INIT_STARTED_AT", std::to_string(start_ms).c_str(), 1);

        char* path = argv[0];
        char* args[] = { path, nullptr };
        execv(path, args);//重新执行main方法，进入第二阶段

        // execv() only returns if an error happened, in which case we
        // panic and never fall through this conditional.
        PLOG(FATAL) << "execv(\"" << path << "\") failed";
    }

    // At this point we're in the second stage of init. 再次 初始化Linux Kernel内核的日志系统
    InitKernelLogging(argv);
    LOG(INFO) << "init second stage started!";

    // Set up a session keyring that all processes will have access to. It
    // will hold things like FBE encryption keys. No process should override
    // its session keyring.
    keyctl_get_keyring_ID(KEY_SPEC_SESSION_KEYRING, 1);

    // Indicate that booting is in progress to background fw loaders, etc.
    close(open("/dev/.booting", O_WRONLY | O_CREAT | O_CLOEXEC, 0000));
    //初始化属性系统，并从指定文件读取属性
    property_init();

    // todo：属性（服务）：相当于Windows系统里面的注册表信息。Windows系统中，程序需要注册之后才能正常的运行。
    // todo：Linux系统则是必须完成初始化（这就相当于Windows里的注册操作），才能正常运行。

    // If arguments are passed both on the command line and in DT,
    // properties set in DT always have priority over the command-line ones.
    // 接下来的一系列操作都是从各个文件读取一些属性，然后通过property_set设置系统属性
    // 1.这句英文的大概意思是，如果参数同时从命令行和DT传过来，DT的优先级总是大于命令行的
    // 2.DT即device-tree，中文意思是设备树，这里面记录自己的硬件配置和系统运行参数，参考 http://www.wowotech.net/linux_kenrel/why-dt.html
    process_kernel_dt();//处理DT属性
    process_kernel_cmdline();//处理命令行属性

    // Propagate the kernel variables to internal variables
    // used by init as well as the current required properties.
    export_kernel_boot_props();//处理其他的一些属性

    // Make the time that init started available for bootstat to log.
    // 将初始化启动的时间，保存到bootstart里面去
    property_set("ro.boottime.init", getenv("INIT_STARTED_AT"));
    property_set("ro.boottime.init.selinux", getenv("INIT_SELINUX_TOOK"));

    // Set libavb version for Framework-only OTA match in Treble build.
    const char* avb_version = getenv("INIT_AVB_VERSION");
    if (avb_version) property_set("ro.boot.avb_version", avb_version);

    // Clean up our environment.
    //清空这些环境变量，因为之前都已经存入到系统属性中去了
    unsetenv("INIT_SECOND_STAGE");
    unsetenv("INIT_STARTED_AT");
    unsetenv("INIT_SELINUX_TOOK");
    unsetenv("INIT_AVB_VERSION");

    // Now set up SELinux for second stage.
    SelinuxSetupKernelLogging();
    SelabelInitialize();
    SelinuxRestoreContext();

    epoll_fd = epoll_create1(EPOLL_CLOEXEC);//创建epoll实例，并返回epoll的文件描述符
    if (epoll_fd == -1) {
        PLOG(FATAL) << "epoll_create1 failed";
    }
    //主要是创建handler处理子进程终止信号，创建一个匿名socket并注册到epoll进行监听
    // 为 SIGCHLD 初始化创建一个 信号处理机制
    sigchld_handler_init();

    if (!IsRebootCapable()) {
        // If init does not have the CAP_SYS_BOOT capability, it is running in a container.
        // In that case, receiving SIGTERM will cause the system to shut down.
        InstallSigtermHandler();
    }

    property_load_boot_defaults();//从文件中加载一些属性，读取usb配置
    export_oem_lock_status();//设置ro.boot.flash.locked 属性
    start_property_service();//开启一个socket监听系统属性的设置
    set_usb_controller();//设置sys.usb.controller 属性
    // 方法映射 “class_start”->  "do_class_start"
    const BuiltinFunctionMap function_map;
    // 1.C++中::表示静态方法调用，相当于java中static的方法
    Action::set_function_map(&function_map);//将function_map存放到Action中作为成员属性

    subcontexts = InitializeSubcontexts();

    ActionManager& am = ActionManager::GetInstance();
    ServiceList& sm = ServiceList::GetInstance();
    // 启动的第三阶段：解析 init.rc配置文件，并启动 zygote 进程
    LoadBootScripts(am, sm);

    // Turning this on and letting the INFO logging be discarded adds 0.2s to
    // Nexus 9 boot time, so it's disabled by default.
    if (false) DumpState();//打印一些当前Parser的信息，默认是不执行的

    am.QueueEventTrigger("early-init");//QueueEventTrigger用于触发Action,这里触发early-init事件

    // Queue an action that waits for coldboot done so we know ueventd has set up all of /dev...
    // QueueBuiltinAction用于添加 Action，第一个参数是Action要执行的Command,第二个是Trigger
    am.QueueBuiltinAction(wait_for_coldboot_done_action, "wait_for_coldboot_done");
    // ... so that we can start queuing up actions that require stuff from /dev.
    am.QueueBuiltinAction(MixHwrngIntoLinuxRngAction, "MixHwrngIntoLinuxRng");
    am.QueueBuiltinAction(SetMmapRndBitsAction, "SetMmapRndBits");
    am.QueueBuiltinAction(SetKptrRestrictAction, "SetKptrRestrict");
    am.QueueBuiltinAction(keychord_init_action, "keychord_init");
    am.QueueBuiltinAction(console_init_action, "console_init");

    // Trigger all the boot actions to get us started.
    am.QueueEventTrigger("init");

    // Repeat mix_hwrng_into_linux_rng in case /dev/hw_random or /dev/random
    // wasn't ready immediately after wait_for_coldboot_done
    am.QueueBuiltinAction(MixHwrngIntoLinuxRngAction, "MixHwrngIntoLinuxRng");

    // Don't mount filesystems or start core system services in charger mode.
    std::string bootmode = GetProperty("ro.bootmode", "");
    if (bootmode == "charger") {
        am.QueueEventTrigger("charger");
    } else {
        am.QueueEventTrigger("late-init");
    }

    // Run all property triggers based on current state of the properties.
    am.QueueBuiltinAction(queue_property_triggers_action, "queue_property_triggers");
    // 在该 while 循环里面，循环解析并获取到服务，然后启动这些服务。
    while (true) {
        // By default, sleep until something happens：epoll_timeout_ms 超时时间，相当于阻塞时间
        int epoll_timeout_ms = -1;

        if (do_shutdown && !shutting_down) {
            do_shutdown = false;
            // 处理电源控制信息
            if (HandlePowerctlMessage(shutdown_command)) {
                shutting_down = true;
            }
        }
        // 当服务没有执行启动运行时，则执行启动执行命令
        if (!(waiting_for_prop || Service::is_exec_service_running())) {
            am.ExecuteOneCommand();// 执行一个command
        }
        // 1.waiting_for_prop和IsWaitingForExec都是判断一个Timer为不为空，相当于一个标志位
        // 2.waiting_for_prop负责属性设置，IsWaitingForExe负责service运行
        // 3.当有属性设置或Service开始运行时，这两个值就不为空，直到执行完毕才置为空
        // 4.其实这两个判断条件主要作用就是保证属性设置和service启动的完整性，也可以说是为了同步
        if (!(waiting_for_prop || Service::is_exec_service_running())) {
            if (!shutting_down) {
                // 重启进程。当某个服务挂了，系统会在这里restart重启它
                auto next_process_restart_time = RestartProcesses();

                // If there's a process that needs restarting, wake up in time for that.
                if (next_process_restart_time) {
                    // 获取服务启动的超时时间
                    epoll_timeout_ms =
                            std::chrono::ceil<std::chrono::milliseconds>(*next_process_restart_time - boot_clock::now()).count();
                    if (epoll_timeout_ms < 0) epoll_timeout_ms = 0;
                }
            }

            // If there's more work to do, wake up again immediately.
            if (am.HasMoreCommands()) epoll_timeout_ms = 0;// 当还有命令要执行时，将epoll_timeout_ms设置为0
        }

        epoll_event ev;
        // 1.epoll_wait与epoll_create1、epoll_ctl是一起使用的
        // 2.epoll_create1用于创建epoll的文件描述符，epoll_ctl、epoll_wait都把它创建的fd作为第一个参数传入
        // 3.epoll_ctl用于操作epoll，EPOLL_CTL_ADD：注册新的fd到epfd中，EPOLL_CTL_MOD：修改已经注册的fd的监听事件，EPOLL_CTL_DEL：从epfd中删除一个fd；
        // 4.epoll_wait用于等待事件的产生，epoll_ctl调用EPOLL_CTL_ADD时会传入需要监听什么类型的事件，
        //   比如EPOLLIN表示监听fd可读，当该fd有可读的数据时，调用epoll_wait经过epoll_timeout_ms时间就会把该事件的信息返回给&ev
        int nr = TEMP_FAILURE_RETRY(epoll_wait(epoll_fd, &ev, 1, epoll_timeout_ms));
        if (nr == -1) {
            PLOG(ERROR) << "epoll_wait failed";
        } else if (nr == 1) {
            ((void (*)()) ev.data.ptr)();
        }
    }

    return 0;
}

}  // namespace init
}  // namespace android
