open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum256_add =
      foreign "Hacl_Bignum256_add"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum256_sub =
      foreign "Hacl_Bignum256_sub"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum256_mul =
      foreign "Hacl_Bignum256_mul"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum256_mod_precompr2 =
      foreign "Hacl_Bignum256_mod_precompr2"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum256_mod =
      foreign "Hacl_Bignum256_mod"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
    let hacl_Bignum256_mod_exp_raw_precompr2 =
      foreign "Hacl_Bignum256_mod_exp_raw_precompr2"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))))
    let hacl_Bignum256_mod_exp_ct_precompr2 =
      foreign "Hacl_Bignum256_mod_exp_ct_precompr2"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))))
    let hacl_Bignum256_mod_exp_raw =
      foreign "Hacl_Bignum256_mod_exp_raw"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Bignum256_mod_exp_ct =
      foreign "Hacl_Bignum256_mod_exp_ct"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Bignum256_new_precompr2 =
      foreign "Hacl_Bignum256_new_precompr2"
        ((ptr uint64_t) @-> (returning (ptr uint64_t)))
    let hacl_Bignum256_mod_inv_prime_raw =
      foreign "Hacl_Bignum256_mod_inv_prime_raw"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
    let hacl_Bignum256_new_bn_from_bytes_be =
      foreign "Hacl_Bignum256_new_bn_from_bytes_be"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint64_t))))
    let hacl_Bignum256_bn_to_bytes_be =
      foreign "Hacl_Bignum256_bn_to_bytes_be"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Bignum256_lt_mask =
      foreign "Hacl_Bignum256_lt_mask"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))
  end