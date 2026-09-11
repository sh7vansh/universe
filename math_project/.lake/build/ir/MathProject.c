// Lean compiler output
// Module: MathProject
// Imports: public import Init public meta import Init public import MathProject.Basic public import MathProject.OntologicalMachine public import MathProject.OntologicalFriction public import MathProject.CategoricalMachine public import MathProject.AdversarialTrap public import MathProject.CategoricalColimits public import MathProject.MatroidFriction
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_math__project_MathProject_Basic(uint8_t builtin);
lean_object* initialize_math__project_MathProject_OntologicalMachine(uint8_t builtin);
lean_object* initialize_math__project_MathProject_OntologicalFriction(uint8_t builtin);
lean_object* initialize_math__project_MathProject_CategoricalMachine(uint8_t builtin);
lean_object* initialize_math__project_MathProject_AdversarialTrap(uint8_t builtin);
lean_object* initialize_math__project_MathProject_CategoricalColimits(uint8_t builtin);
lean_object* initialize_math__project_MathProject_MatroidFriction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_math__project_MathProject(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_OntologicalMachine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_OntologicalFriction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_CategoricalMachine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_AdversarialTrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_CategoricalColimits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_math__project_MathProject_MatroidFriction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
