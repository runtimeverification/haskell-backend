# Pathological cases of `add-module` request sequences

(NB `name-as-id` is false in all requests where it is not explicitly mentioned).

* _add_module_twice_
  - sends the same request twice.
  Should succeed.
* _add_module_twice_with_name_
  - sends the same request twice with `name-as-id`.
  Should succeed.
* _add_module_with_hash_name_as_id_first_fails_
  - For an a-priori known module `B`:
    - first sends a `module m<hash of B>` with `name-as-id`,
    - then sends the module `B`.
    Should fail with error mentioning `m<hash of B>`.
* _add_module_with_hash_name_as_id_second_fails_
  - For an a-priori known module `A`:
    - first sends module `A`,
    - then sends a `module m<hash-of-A>` with `name-as-id`.
  Should fail with error mentioning `m<hash-of-A`.
* _add_module_with_hash_name_not_as_id_first_
  - For an a-priori known module `C`:
    - First sends a `module m<hash of C>`,
    - then sends module `C`.
    Should succeed.
* _add_module_with_hash_name_not_as_id_second_
  - For an a-priori known module `A`:
    - first sends module `A`,
    - then sends a `module m<hash-of-A>`.
  Should succeed.
* _add_module_with_import_
  - For an a-priori known module `A`
    - first sends `module A` with `name-as-id`,
    - and then sends a module `B` that imports `m<hash of A>`.
  Should succeed.
* _add_module_with_named_import_
  - First sends `module A` with `name-as-id`,
  - and then sends a module `B` that imports `A`.
  Should succeed.
* _add_module_with_name_then_without_name_
  - sends the same module twice, the first time with `name-as-id`.
  Should succeed.
* _add_module_without_name_then_with_name_
  - sends the same module twice, the second time with `name-as-id`.
  Should succeed.
* _add_module_with_unknown_import_fails_
  - sends a module that imports an `UNKNOWN` module.
  Should fail mentioning the `UNKNOWN` module.
* _add_module_with_unknown_named_import_fails_
  - First sends `module UNKNOWN`,
  - then sends a module that imports `UNKNOWN`.
  Should fail mentioning the `UNKNOWN` module.
