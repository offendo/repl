#include <stdio.h>
#include <lean/lean.h>
#include <stdlib.h>
#include <inttypes.h>


extern void lean_initialize();
extern void lean_initialize_runtime_module();
extern void lean_init_search_path(lean_obj_arg);
extern void lean_init_task_manager();
extern void lean_initialize_runtime_module();
extern void lean_io_mark_end_initialization();

extern lean_object* do_init();
extern lean_object* run_json_command(lean_obj_arg);
extern lean_object* process_input_singleton(lean_obj_arg);
extern lean_object* process_input_empty_state(lean_obj_arg);
extern lean_object* process_input_from_state(lean_obj_arg, lean_obj_arg);
extern lean_object* process_input_with_timeout(uint32_t timeout, lean_obj_arg str);
extern lean_object* process_input_with_timeout_from_state(uint32_t timeout, lean_obj_arg str, lean_obj_arg state);
extern lean_object *initialize_REPL_Frontend(uint8_t builtin, lean_object *);
extern lean_object *initialize_REPL_Main(uint8_t builtin, lean_object *);

lean_object * process(uint32_t, char* );

int main(int argv, char** argc) {
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
      return 1;  // do not access Lean declarations if initialization failed
  }
  lean_init_task_manager();
  lean_io_mark_end_initialization();

  // actual program
  uint32_t timeout = 50;
  //do_init();
  lean_object* output = process(timeout, "def x : Real := 5.5\ndef y : Real := 6.5\n#eval x + y\n");
  return 0;
}

lean_object * process(uint32_t timeout, char* input){
  lean_object * output1;
  lean_object * output2;
  lean_object* lean_cmd1;
  lean_object* lean_cmd2;
  lean_object * obj;
  lean_object * env;
  lean_object * msgs;
  lean_object * trees;

  // size_t len = (size_t) snprintf(NULL, 0, format);
  // char* cmd = malloc(len);
  /* Safely write to mystr with known length 'len' */
  // snprintf(cmd, len, format);

  // printf("Initial: %s\n", cmd);
  lean_cmd1 = lean_mk_string("import Mathlib\ndef x : Nat := 5\n");
  output1 = process_input_with_timeout(timeout, lean_cmd1);

  if (lean_io_result_is_ok(output1)) {
    printf("Hooray!\n");
    obj   = lean_ctor_get(output1, 0);
    env   = lean_ctor_get(obj, 0);
    msgs  = lean_ctor_get(obj, 1);
    trees = lean_ctor_get(obj, 2);
    printf("msgs: %s\n", lean_string_cstr(msgs));
    // printf("trees: %s\n", lean_string_cstr(trees));
  } else {
    printf("Boo...\n");
    return NULL;
  }

  lean_cmd2 = lean_mk_string("def y : Nat := 8\n#eval x + y");
  output2 = process_input_with_timeout_from_state(timeout, lean_cmd2, env);

  if (lean_io_result_is_ok(output2)) {
    obj = lean_ctor_get(output2, 0);
    env = lean_ctor_get(obj, 0);
    msgs = lean_ctor_get(obj, 1);
    trees = lean_ctor_get(obj, 2);
    printf("msgs: %s\n", lean_string_cstr(msgs));
    return output2;
  }
  return NULL;
}
