Require Import CompilerRuntime Types.
(* Context {m:brand_relation}. *)
Module CompType(runtime:CompilerRuntime).
  Require RType String.

  Definition record_kind : Set
    := RType.record_kind.

  Definition open_kind : record_kind
    := RType.Open.

  Definition closed_kind : record_kind
    := RType.Closed.

  Definition camp_type {m:brand_relation} : Set
    := RType.rtype.
  Definition t {m:brand_relation} : Set
    := camp_type.

  Definition sorted_pf_type {m:brand_relation} srl
      := RSort.is_list_sorted RBindings.ODT_lt_dec (@RAssoc.domain String.string camp_type srl) = true.

  Definition bottom {m:brand_relation} : camp_type
    := RType.Bottom.  
  Definition top {m:brand_relation} : camp_type
    := RType.Top.
  Definition unit {m:brand_relation} : camp_type
    := RType.Unit.
  Definition nat {m:brand_relation} : camp_type
    := RType.Nat.
  Definition bool {m:brand_relation} : camp_type
    := RType.Bool.
  Definition string {m:brand_relation} : camp_type
    := RType.String.
  Definition bag {m:brand_relation} : camp_type -> camp_type
    := RType.Coll.
  Definition record {m:brand_relation} : record_kind -> forall (r:list (String.string*camp_type)), sorted_pf_type r -> camp_type
    := RType.Rec.
  Definition either {m:brand_relation} : camp_type -> camp_type -> camp_type
    := RType.Either.
  Definition arrow {m:brand_relation} : camp_type -> camp_type -> camp_type
    := RType.Arrow.
  Definition brand {m:brand_relation} : list String.string -> camp_type
    := RType.Brand.

  (* Additional support for brand models extraction -- will have to be tested/consolidated *)
  Require Import TypingRuntime.

  Definition brand_model : Set := brand_model.
  Definition make_brand_model := make_brand_model_fails.
  Definition typing_runtime : Set := typing_runtime.

  (* Additional support for json to rtype conversion *)
  Require Import JSONtoData.
  
  Definition json_to_rtype {m:brand_relation} := json_to_rtype.  

  (* JSON -> sdata string *)
  Require SparkData.

  Definition json_to_sjson br (m:brand_model) : JSON.json -> JSON.json -> option String.string
    := @SparkData.json_to_sjson _ br _ _ m _.

End CompType.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
