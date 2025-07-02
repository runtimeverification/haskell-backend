#ifndef KLLVM_C_H
#define KLLVM_C_H

#ifndef __cplusplus
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#else
#include <cstddef>
#include <cstdint>
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Error Handling
 * ==============
 *
 * Some API functions in these bindings can bubble up internal errors from the
 * LLVM backend to avoid crashing the host process.
 *
 * These functions take an initial parameter of type `kore_error *`; if that
 * parameter is `NULL` then any C++ exceptions thrown by the backend will
 * simply be rethrown and the host process will crash with the relevant error
 * message.
 *
 * If the input is not NULL, then the object will have call-specific information
 * filled in that can be accessed using the getter functions in this section.
 */

typedef struct kore_error kore_error;

/**
 * Create an empty error object. Initially, the created object will report
 * success (not failure), and will return `NULL` if its message is accessed.
 */
kore_error *kore_error_new(void);

/**
 * Return true if no error occurred when this object was passed to an API call.
 */
bool kore_error_is_success(kore_error const *);

/**
 * Return any error-specific message that has been added to this object. The
 * returned string is a reference to the error's internal state and should not
 * be freed separately. If no error has occurred (i.e. is_success returns true),
 * then return NULL.
 */
char const *kore_error_message(kore_error const *);

/**
 * Deallocate an error and its associated message.
 */
void kore_error_free(kore_error *);

/*
 * Binary KORE Outputs
 * ===================
 *
 * All API functions in these bindings that return binary KORE data do so with a
 * pair of output parameters:
 *
 *   char   ** data_out
 *   size_t  * size_out
 *
 * The returned binary data in *data_out has length *size_out, and should be
 * freed with free(*data_out) when it is no longer required.
 */

/* Opaque types */

typedef struct kore_pattern kore_pattern;
typedef struct kore_sort kore_sort;
typedef struct kore_symbol kore_symbol;
typedef struct block block;

/* kore_pattern */

char *kore_pattern_dump(kore_pattern const *);

char *kore_pattern_pretty_print(kore_pattern const *);

void kore_pattern_serialize(kore_pattern const *, char **, size_t *);

void kore_pattern_free(kore_pattern const *);

kore_pattern *kore_pattern_parse(char const *);
kore_pattern *kore_pattern_parse_file(char const *);

kore_pattern *kore_pattern_new_token(char const *, kore_sort const *);
kore_pattern *
kore_pattern_new_token_with_len(char const *, size_t, kore_sort const *);

kore_pattern *kore_pattern_new_injection(
    kore_pattern const *, kore_sort const *, kore_sort const *);

kore_pattern *
kore_pattern_make_interpreter_input(kore_pattern const *, kore_sort const *);

kore_pattern *kore_composite_pattern_new(char const *);
kore_pattern *kore_composite_pattern_from_symbol(kore_symbol *);
void kore_composite_pattern_add_argument(kore_pattern *, kore_pattern const *);

kore_pattern *kore_pattern_desugar_associative(kore_pattern const *);

kore_pattern *kore_string_pattern_new(char const *);
kore_pattern *kore_string_pattern_new_with_len(char const *, size_t);

block *kore_pattern_construct(kore_pattern const *);
char *kore_block_dump(block *);

kore_pattern *kore_pattern_from_block(block *);

/*
 * Expects the argument term to be of the form:
 *   sym{}(BOOL)
 */
bool kore_block_get_bool(block *);

bool kore_simplify_bool(kore_error *, kore_pattern const *);

void kore_simplify(
    kore_error *err, kore_pattern const *pattern, kore_sort const *sort,
    char **, size_t *);

void kore_simplify_binary(
    kore_error *, char *, size_t, kore_sort const *, char **, size_t *);

block *take_steps(int64_t depth, block *term);

void init_static_objects(void);

/* kore_sort */

char *kore_sort_dump(kore_sort const *);

void kore_sort_free(kore_sort const *);

bool kore_sort_is_concrete(kore_sort const *);

bool kore_sort_is_kitem(kore_sort const *);
bool kore_sort_is_k(kore_sort const *);

kore_sort *kore_composite_sort_new(char const *);
void kore_composite_sort_add_argument(kore_sort const *, kore_sort const *);

/* kore_symbol */

kore_symbol *kore_symbol_new(char const *);

void kore_symbol_free(kore_symbol const *);

void kore_symbol_add_formal_argument(kore_symbol *, kore_sort const *);

/* Memory management */

void kllvm_init(void);
void kllvm_free_all_memory(void);

/* Sort-specific functions */

bool kllvm_mutable_bytes_enabled(void);

/* Definitions */

/**
 * Parse the given KORE definition, then if any of its axioms have a `label`
 * attribute that matches the supplied label, return the name of the function
 * symbol that attempts matching a pattern against that axiom (and will
 * therefore populate the backend's global matching log).
 *
 * If no such axiom exists, return `nullptr`.
 */
char *kore_match_function_name(char const *defn_path, char const *label);

#ifdef __cplusplus
}
#endif

#endif
