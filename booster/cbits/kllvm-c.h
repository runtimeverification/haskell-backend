#ifndef KLLVM_C_H
#define KLLVM_C_H

#ifdef __cplusplus
extern "C" {
#endif


typedef struct kore_pattern kore_pattern;

char *kore_pattern_dump(kore_pattern const *);

void kore_pattern_free(kore_pattern const *);

kore_pattern *kore_composite_pattern_new(char const *);
void kore_composite_pattern_add_argument(kore_pattern *, kore_pattern *);

kore_pattern *kore_string_pattern_new(char const *);

#ifdef __cplusplus
}
#endif

#endif
