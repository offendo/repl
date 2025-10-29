#include <pybind11/pybind11.h>
#include <lean/lean.h>
#include <cstdint>
#include <stdexcept>
#include <string>

#include <stdlib.h>
#include <inttypes.h>

namespace py = pybind11;

extern"C" void lean_initialize();
extern"C" void lean_initialize_runtime_module();
extern"C" void lean_init_search_path(lean_obj_arg);
extern"C" void lean_init_task_manager();
extern"C" void lean_initialize_runtime_module();
extern"C" void lean_io_mark_end_initialization();

extern"C" lean_object* do_init();
extern"C" lean_object* run_json_command(lean_obj_arg);
extern"C" lean_object* process_input_singleton(lean_obj_arg);
extern"C" lean_object* process_input_empty_state(lean_obj_arg);
extern"C" lean_object* process_input_from_state(lean_obj_arg, lean_obj_arg);
extern"C" lean_object* process_input_with_timeout(uint32_t timeout, lean_obj_arg str);
extern"C" lean_object* process_input_with_timeout_from_state(uint32_t timeout, lean_obj_arg str, lean_obj_arg state);
extern"C" lean_object *initialize_REPL_Frontend(uint8_t builtin, lean_object *);
extern"C" lean_object *initialize_REPL_Main(uint8_t builtin, lean_object *);


void cleanup_lean_object(void* ptr) {
    // This function is called when the capsule is destroyed
    delete static_cast<lean_object*>(ptr);
}

PYBIND11_MODULE(lean_process, m) {
    m.def("process_input_with_timeout", [](uint32_t timeout, const std::string &input) -> const char* {
        lean_initialize();
        lean_initialize_runtime_module();
        // use same default as for Lean executables
        uint8_t builtin = 1;
        lean_init_search_path(lean_io_mk_world());
        lean_object * res = initialize_REPL_Frontend(builtin, lean_io_mk_world());
        if (lean_io_result_is_ok(res)) {
            lean_dec_ref(res);
        } else {
            lean_io_result_show_error(res);
            lean_dec(res);
            return "error";  // do not access Lean declarations if initialization failed
        }
        lean_init_task_manager();
        lean_io_mark_end_initialization();
        lean_object *lean_input = lean_mk_string(input.c_str());
        lean_object *result = process_input_with_timeout(timeout, lean_input);
        lean_object* obj = lean_ctor_get(result, 0);
        lean_object* env = lean_ctor_get(obj, 0);
        lean_object* msgs = lean_ctor_get(obj, 1);
        const char* msg_str = lean_string_cstr(msgs);
        return msg_str;
    });

    m.def("process_input_with_timeout_from_state", [](uint32_t timeout, const std::string &input, lean_object *state) -> const char* {
        lean_initialize();
        lean_initialize_runtime_module();
        // use same default as for Lean executables
        uint8_t builtin = 1;
        lean_init_search_path(lean_io_mk_world());
        lean_object * res = initialize_REPL_Frontend(builtin, lean_io_mk_world());
        if (lean_io_result_is_ok(res)) {
            lean_dec_ref(res);
        } else {
            lean_io_result_show_error(res);
            lean_dec(res);
            return "error";  // do not access Lean declarations if initialization failed
        }
        lean_init_task_manager();
        lean_io_mark_end_initialization();
        lean_object *lean_input = lean_mk_string(input.c_str());
        lean_object *result = process_input_with_timeout_from_state(timeout, lean_input, state);
        lean_object* obj = lean_ctor_get(result, 0);
        lean_object* env = lean_ctor_get(obj, 0);
        lean_object* msgs = lean_ctor_get(obj, 1);
        const char* msg_str = lean_string_cstr(msgs);
        return msg_str;
    });
}
