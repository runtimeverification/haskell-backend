#ifndef KLLVM_C_H
#define KLLVM_C_H

#ifndef __cplusplus
#include <stdbool.h>
#include <stddef.h>
#else
#include <cstddef>
#endif

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Memory management in KLLVM-C
 * ============================
 *
 * The underlying C++ AST library manages Pattern and Sort objects differently;
 * Patterns have a *unique* ownership model, while Sorts are *shared*. This
 * means that a composite pattern object owns its arguments, and will delete
 * them when it is destructed. Conversely, the same sort object could be an
 * argument to two different composite sorts, and would only be destroyed when
 * both of those owners are (via reference-counting from std::shared_ptr).
 *
 * These differences are exposed in the C API essentially unmodified; functions
 * that take an opaque pattern object will modify the opaque holder such that it
 * is not usable after the call (i.e. the underlying unique_ptr has been
 * moved-from). This is not true for the analogous functions on sorts. The C API
 * reflects this difference by const-qualification of pointer arguments.
 *
 * Note that these different models *do not* apply to the opaque holder objects
 * allocated by the C *_new functions; the holder should be deallocated with the
 * corresponding *_free function when it is no longer required. Doing so will
 * handle calling the appropriate destructor of the held object (e.g. freeing a
 * kore_pattern will destroy the underlying object held by the
 * std::unique_ptr<KOREPattern> inside it).
 */

/* Opaque types */

typedef struct kore_pattern kore_pattern;
typedef struct kore_sort kore_sort;
typedef struct kore_symbol kore_symbol;
typedef struct block block;

/* KOREPattern */

char *kore_pattern_dump(kore_pattern const *);

void kore_pattern_free(kore_pattern const *);

kore_pattern *kore_pattern_new_token(char const *, kore_sort const *);
kore_pattern *
kore_pattern_new_token_with_len(char const *, size_t, kore_sort const *);

kore_pattern *kore_pattern_new_injection(
    kore_pattern *, kore_sort const *, kore_sort const *);

kore_pattern *kore_pattern_make_interpreter_input(kore_pattern *);

kore_pattern *kore_composite_pattern_new(char const *);
kore_pattern *kore_composite_pattern_from_symbol(kore_symbol *);
void kore_composite_pattern_add_argument(kore_pattern *, kore_pattern *);

kore_pattern *kore_string_pattern_new(char const *);
kore_pattern *kore_string_pattern_new_with_len(char const *, size_t);

block *kore_pattern_construct(kore_pattern const *);
char *kore_block_dump(block *);

/* 
 * Expects the argument term to be of the form:
 *   sym{}(BOOL)
 */
bool kore_block_get_bool(block *);

bool kore_simplify_bool(kore_pattern *);

/*
 * The two final parameters here are outputs: the serialized binary data and the
 * number of serialized bytes, respectively. The binary data should be freed
 * with `free()`.
 */
void kore_simplify(kore_pattern *pattern, kore_sort *sort, char **, size_t *);

/* KORESort */

char *kore_sort_dump(kore_sort const *);

void kore_sort_free(kore_sort const *);

bool kore_sort_is_concrete(kore_sort const *);

bool kore_sort_is_kitem(kore_sort const *);

kore_sort *kore_composite_sort_new(char const *);
void kore_composite_sort_add_argument(kore_sort const *, kore_sort const *);

/* KORESymbol */

kore_symbol *kore_symbol_new(char const *);

void kore_symbol_free(kore_symbol const *);

void kore_symbol_add_formal_argument(kore_symbol *, kore_sort const *);

#ifdef __cplusplus
}
#endif

#endif
