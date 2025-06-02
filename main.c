#include <stdio.h>
#include <lean/lean.h>
#include <stdlib.h>


extern void lean_initialize();
extern void lean_init_search_path(lean_obj_arg);
extern void lean_init_task_manager();
extern void lean_initialize_runtime_module();
extern void lean_io_mark_end_initialization();

extern lean_object* process_input_with_timeout(uint32_t timeout, lean_obj_arg str);
extern lean_object* process_input_with_timeout_from_state(uint32_t timeout, lean_obj_arg str, lean_obj_arg state);
extern lean_object *initialize_REPL_Frontend(uint8_t builtin, lean_object *);

lean_object * process(uint32_t, char* );

int main(int argv, char** argc) {
  lean_initialize();
  // use same default as for Lean executables
  uint8_t builtin = 1;
  lean_init_search_path(lean_io_mk_world());
  lean_object * res = initialize_REPL_Frontend(builtin, lean_io_mk_world());
  if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
  } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      return 1;  // do not access Lean declarations if initialization failed
  }
  lean_init_task_manager();
  lean_io_mark_end_initialization();

  // actual program
  const uint32_t timeout = 45;
  lean_object* output = process(timeout, "import Mathlib\n;def x : Nat := 5\n#print x");

  lean_ctor_get(output, 
  return 0;
}

lean_object * process(uint32_t timeout, char* input){
  lean_object* str = lean_mk_string(input);
  lean_object* output = process_input_with_timeout(timeout, str);
  return output;
}
