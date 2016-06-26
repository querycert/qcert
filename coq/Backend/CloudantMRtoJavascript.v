(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Require Import List String.

Require Import Utils BasicRuntime.
Require Import NNRCRuntime CloudantMR.
Require Import NNRCtoJavascript.
Require Import ForeignToJavascript ForeignCloudant.

Local Open Scope string_scope.

Section CloudantMRtoJavascript.

  Context {fruntime:foreign_runtime}.
  Context {ftojavascript:foreign_to_javascript}.
  Context {fcloudant:foreign_cloudant}.

  Section MRJS.

    (* Java equivalent: CloudantBackend.emitIdToString *)
    Definition emitIdToString (vkey vout:string) (eol:string) (quotel:string) : string :=
      "  emit(" ++ vkey ++ ", " ++ vout ++ ");" ++ eol.

    (* Java equivalent: CloudantBackend.emitConstIdToString *)
    Definition emitConstIdToString (n:nat) (vkey vout:string) (eol:string) (quotel:string) : string :=
      "  emit(" ++ (nat_to_string10 n) ++ ", " ++ vout ++ ");" ++ eol.
    
    (* Java equivalent: CloudantBackend.emitConstToString *)
    Definition emitConstToString (n:nat) (vkey vout:string) (eol:string) (quotel:string) : string :=
        "  for (var srcout="
          ++ vout ++ ", iout=0; iout<" ++ vout ++ ".length; iout++) {" ++ eol
          ++ "    emit(" ++ (nat_to_string10 n) ++ ",srcout[iout]);" ++ eol
          ++ "  }" ++ eol.
    
    (* Java equivalent: CloudantBackend.emitInventToString *)
    Definition emitInventToString (vkey vout:string) (eol:string) (quotel:string) : string :=
        "  for (var srcout="
          ++ vout ++ ", iout=0; iout<" ++ vout ++ ".length; iout++) {" ++ eol
          ++ "    emit(" ++ vkey ++ ".concat(iout),srcout[iout]);" ++ eol
          ++ "  }" ++ eol.

    (* Java equivalent: CloudantBackend.createMapFunFirst *)
    Definition createMapFunFirst (v_map:string) (e:nrc) (emitString:string) (harness:bool) (eol:string) (quotel:string) : string :=
          let '(j0, v0, t0) := nrcToJSunshadow e 1 1 eol quotel (v_map::nil) ((v_map,"doc")::nil) in
          "function (doc) {" ++ eol
                             ++ "  var v0 = null;" ++ eol
                             ++ "  var key = doc._id;" ++ eol
                             ++ "  var doc = unwrap(doc);" ++ eol
                             ++ "  if (doc != null) {" ++ eol
                             ++ j0
                             ++ "  var out = " ++ v0 ++ ";" ++ eol
                             ++ emitString ++ eol
                             ++ "  }"
                             ++ (if harness then " %HARNESS% " else "")
                             ++ "}".
    
    (* Java equivalent: CloudantBackend.createMapFunRest *)    
    Definition createMapFunRest (v_map:string) (e:nrc) (emitString:string) (harness:bool) (eol:string) (quotel:string) : string :=
          let '(j0, v0, t0) := nrcToJSunshadow e 1 1 eol quotel (v_map::nil) ((v_map,"doc")::nil) in
          "function (doc) {" ++ eol
                             ++ "  var v0 = null;" ++ eol
                             ++ "  var key = doc.key;" ++ eol
                             ++ "  var doc = doc.value;" ++ eol
                             ++ j0
                             ++ "  var out = " ++ v0 ++ ";" ++ eol
                             ++ emitString ++ eol
                             ++ (if harness then " %HARNESS% " else "")
                             ++ "}".

    (* Java equivalent: CloudantBackend.nrcToJSMapFirst *)    
    Definition nrcToJSMapFirst (cldmap:cld_map) (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) : string :=
      match map_fun cldmap with
      | CldMapId (v_map, e) =>
        match map_emit cldmap with
        | CldEmitDist =>
          createMapFunFirst v_map e (emitIdToString "key" "out" eol quotel) harness eol quotel
        | CldEmitCollect index =>
          createMapFunFirst v_map e (emitConstIdToString index "key" "out" eol quotel) harness eol quotel
        end
      | CldMapFlatten (v_map, e) =>
        match map_emit cldmap with
        | CldEmitDist =>
          createMapFunFirst v_map e (emitInventToString "key" "out" eol quotel) harness eol quotel
        | CldEmitCollect index =>
          createMapFunFirst v_map e (emitConstToString index "key" "out" eol quotel) harness eol quotel
        end
      end.

    (* Java equivalent: CloudantBackend.nrcToJSMapRest *)    
    Definition nrcToJSMapRest (cldmap:cld_map) (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) : string :=
      match map_fun cldmap with
      | CldMapId (v_map, e) =>
        match map_emit cldmap with
        | CldEmitDist =>
          createMapFunRest v_map e (emitIdToString "key" "out" eol quotel) harness eol quotel
        | CldEmitCollect index =>
          createMapFunRest v_map e (emitConstIdToString index "key" "out" eol quotel) harness eol quotel
        end
      | CldMapFlatten (v_map, e) =>
        match map_emit cldmap with
        | CldEmitDist =>
          createMapFunRest v_map e (emitInventToString "key" "out" eol quotel) harness eol quotel
        | CldEmitCollect index =>
          createMapFunRest v_map e (emitConstToString index "key" "out" eol quotel) harness eol quotel
        end
      end.

	(* Java equivalent: CloudantBackend.nrcToJSReduce *)
    Definition nrcToJSReduce (e1:nrc) (e2:nrc) (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) (values_iv:string) : string :=
      let '(j0, v0, t0) := nrcToJSunshadow e1 1 1 eol quotel (values_iv::nil) ((values_iv,"values")::nil) in
      let '(j1, v1, t1) := nrcToJSunshadow e2 t0 1 eol quotel (values_iv::nil) ((values_iv,"values")::nil) in
      "function (keys, values, rereduce) {" ++ eol
                                            ++ "  if (rereduce) {" ++ eol
                                            ++ j1
                                            ++ "    return " ++ v1 ++ ";" ++ eol
                                            ++ "  }" ++ eol
                                            ++ "  else {" ++ eol
                                            ++ j0
                                            ++ "    return " ++ v0 ++ ";" ++ eol
                                            ++ "  }" ++ eol
                                            ++ (if harness then " %HARNESS% " else "")
                                            ++ "}".

	(* Java equivalent: CloudantBackend.isJSReduce *)
    Definition idJSReduce (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) : string :=
      "function (keys, values, rereduce) {" ++ eol
                                            ++ "   return values[0];" ++ eol
                                            ++ "}".

	(* Java equivalent: CloudantBackend.nrcToJSDefault *)
    Definition nrcToJSDefault (harness:bool) (e_def:nrc) (eol:string) (quotel:string) :=
      let '(j0, v0, t0) := nrcToJSunshadow e_def 1 1 eol quotel nil nil in
      nrcToJSFunStub harness e_def eol quotel nil "db_default".
    
	(* Java equivalent: CloudantBackend.nrcToJSGen *)
    Definition nrcToJSGen (harness:bool) (e_closure:(list var) * nrc) (eol:string) (quotel:string) :=
      let (params, e) := e_closure in
      nrcToJSFunStub harness e eol quotel params "db_post".
    
    Definition mapReduceStringstoJS_pair (eol:string) (index:nat) (mr:option string * option string * option string * option string * string) : string :=
      match mr with
      | (i,o,def,None,m) =>
        let iname :=
            match i with
            | None => "INPUT"
            | Some s => s
            end
        in
        let oname :=
            match o with
            | None => "RESULT"
            | Some s => s
            end
        in
        "// Input DB: " ++ iname ++ eol
                        ++ "// Output DB: " ++ oname ++ eol
                        ++ "// Map Nb " ++ (nat_to_string10 index) ++ eol ++ m ++ eol ++ eol
      | (i,o,def, Some r, m) =>
        let iname :=
            match i with
            | None => "INPUT"
            | Some s => s
            end
        in
        let oname :=
            match o with
            | None => "RESULT"
            | Some s => s
            end
        in
        "// Input DB: " ++ iname ++ eol
                        ++ "// Output DB: " ++ oname ++ eol
                        ++ "// Map Nb " ++ (nat_to_string10 index) ++ eol ++ m ++ eol
                        ++ "// Reduce Nb " ++ (nat_to_string10 index) ++ eol ++ r ++ eol ++ eol
      end.

    Definition mapReduceStringstoJS (eol:string) (mrp:list (option string * option string * option string * option string * string)) : string :=
      fst (fold_right (fun x y => (append (mapReduceStringstoJS_pair eol (snd y) x) (fst y), S (snd y))) ("",0) mrp).
  
  End MRJS.

  Section CloudantJS.
    
    (* Java equivalent: CloudantBackend.cldmrToJS *)
    Definition cldmrToJS (h:list (string*string)) (ini:bool) (harness:bool) (eol:string) (quotel:string) (mr:cld_mr) : option string * option string * option string * option string * string :=
      let v_input := cld_mr_input mr in
      let vs_input := Some v_input in
      let cldmap := cld_mr_map mr in
      let clddefault := cld_mr_reduce_default mr in
      let map_string :=
          if ini
          then nrcToJSMapFirst cldmap h harness eol quotel
          else nrcToJSMapRest cldmap h harness eol quotel
      in
      let default_string :=
          match clddefault with
          | None => None
          | Some clddef =>
            Some (nrcToJSDefault harness clddef eol quotel)
          end
      in
      match cld_mr_reduce mr with
      | None =>
        (vs_input, None, default_string, None, map_string)
      | Some mred =>
        let v_output := reduce_output mred in
        let vs_output :=
            match v_output with
            | None => None
            | Some v => Some v
            end
        in
        match mred.(reduce_fun) with
        | CldRedId =>
          let reduce_string := idJSReduce h harness eol quotel in
          (vs_input, vs_output, default_string, Some reduce_string, map_string)
        | CldRedAggregate (vs_reduce, f_reduce) (v_rereduce, f_rereduce) =>
          let (v_key, v_reduce) := vs_reduce in
          let reduce_string := nrcToJSReduce f_reduce f_rereduce h harness eol quotel v_reduce in
          (vs_input, vs_output, default_string, Some reduce_string, map_string)
        | CldRedOp CldRedOpCount =>
          (vs_input, vs_output, default_string, Some "_count", map_string)
        | CldRedOp (CldRedOpSum _) =>
          (vs_input, vs_output, default_string, Some "_sum", map_string)
        | CldRedOp (CldRedOpStats _) =>
          (vs_input, vs_output, default_string, Some "_stats", map_string)
        end
      end.

    (* Java equivalent: CloudantBackend.cld_mr_chainToJS *)
    Definition cld_mr_chainToJS (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) (mrl:list cld_mr) : list (option string * option string * option string * option string * string) :=
      match mrl with
      | nil => nil
      | mr1 :: mrl' =>
        (cldmrToJS h true harness eol quotel mr1)
          :: (map (cldmrToJS h false harness eol quotel) mrl')
      end.

    (* Java equivalent: CloudantBackend.cld_mrToJS *)
    Definition cld_mrToJS (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) (mrl:cld_mrl) : list (option string * option string * option string * option string * string) :=
      cld_mr_chainToJS h harness eol quotel mrl.(cld_mr_chain).

    (* Java equivalent: CloudantBackend.cld_mrToLastJS *)
    Definition cld_mrToLastJS (h:list (string*string)) (harness:bool) (eol:string) (quotel:string) (e_closure: (list var) * nrc) : string :=
      nrcToJSGen harness e_closure eol quotel.

    (* Java equivalent: CloudantBackend.buildDesignDoc *)
    Definition buildDesignDoc (view_name:string) (s_map:string) (s_reduce:option string) (s_dboutput:option string) (s_dbdefault:option string) :=
      let dmap := ("map", dstring s_map) in
      let dreduce :=
          match s_reduce with
          | None => nil
          | Some s_r => ("reduce", dstring s_r)::nil
          end
      in
      let dbcopy :=
          match s_dboutput with
          | None => nil
          | Some s_db => ("dbcopy", dstring (view_name ++ s_db))::nil
          end
      in
      let dbdefault :=
          match s_dbdefault with
          | None => nil
          | Some s_dbd => ("dbdefault", dstring s_dbd)::nil
          end
      in
      drec (("views", drec ((view_name, drec (dmap::(List.app dreduce (List.app dbcopy dbdefault))))::nil))::nil).


    (* Java equivalent: CloudantBackend.db_of_var *)    
    Definition db_of_var (rulename:string) (var:string) : string := rulename ++ var.
    
	(* Java equivalent: CloudantBackend.makeInputDb *)
    Definition makeInputDB (rulename:string) (ins: option string) : string :=
      match ins with
      | None => rulename
      | Some x => db_of_var rulename x
      end.

	(* Java equivalent: CloudantBackend.makeInputDesignDoc *)
    Definition makeInputDesignDoc (quotel:string) (rulename:string) (mrp:option string * option string * option string * option string * string) : string * string :=
      match mrp with
      | (inputdb, outputdb, defaultdb, mreduce, mmap) =>
        (makeInputDB rulename None, dataToJS quotel (buildDesignDoc rulename mmap mreduce outputdb defaultdb))
      end.
    
    (* Java equivalent: CloudantBackend.makeDesignDoc *)
    Definition makeDesignDoc (quotel:string) (rulename:string) (mrp:option string * option string * option string * option string * string) : string * string :=
      match mrp with
      | (inputdb, outputdb, defaultdb, mreduce, mmap) =>
        (makeInputDB rulename inputdb, dataToJS quotel (buildDesignDoc rulename mmap mreduce outputdb defaultdb))
      end.
    
    (* Java equivalent: CloudantBackend.makeCloudantDesignDocs *)
    Definition makeCloudantDesignDocs (quotel:string) (rulename:string) (mrp:list (option string * option string * option string * option string * string)) : list (string * string) :=
      List.map (fun x => makeDesignDoc quotel rulename x) mrp.
    
    (* Java equivalent: CloudantBackend.makeCloudantDesignDocsTop *)
    Definition makeCloudantDesignDocsTop
               (quotel:string)
               (rulename:string)
               (mrp:list (option string * option string * option string * option string * string))
               (last_expr:string)
               (cld_eff:list string)
      : (list (string * string)) * (string * list string) :=
      match mrp with
      | nil => (nil,(last_expr, cld_eff))
      | x :: nil => ((makeInputDesignDoc quotel rulename x) :: nil, (last_expr, cld_eff))
      | x :: mrp' => ((makeInputDesignDoc quotel rulename x) :: (makeCloudantDesignDocs quotel rulename mrp'), (last_expr, cld_eff))
     end.
    
    Definition makeOneCurl (mrp: string*string) : string :=
      match mrp with
      | (dbname,design) =>
        "curl -X PUT ""https://fe0a4004-9ff8-4bc4-9de8-906e1831cc78-bluemix:8a67972aa73304b3b7cc9b0cc4525d2e6c26988dd08c787ae29d5d68079c0b54@fe0a4004-9ff8-4bc4-9de8-906e1831cc78-bluemix.cloudant.com/" ++ dbname ++ "/_design/" ++ dbname ++ """ -H 'Content-type: application/json' -d '" ++ design ++ "'" ++ eol_newline
      end.

    (* Java equivalent: CloudantBackend.mapReduceStringstoDesignDocs *)
    Definition mapReduceStringstoDesignDocs (mrp:list (option string * option string * option string * option string * string)) (last_expr:string) (cld_eff:list string) (rulename:string) : (list (string*string)) * (string * list string):=
      makeCloudantDesignDocsTop quotel_double rulename mrp last_expr cld_eff.

    (* Java equivalent: CloudantBackend.cld_mrParamsLast *)
    Definition cld_mrParamsLast (rulename:string) (params:list var) :=
      map (db_of_var rulename) params.

    (* Java equivalent: CloudantBackend.mapReducePairstoCloudant *)    
    Definition mapReducePairstoCloudant (h:list (string*string)) (mrl : cld_mrl) (rulename:string) : (list (string*string) * (string * list string)) :=
      let mrpl := cld_mrToJS h true eol_backn quotel_backdouble mrl in
      let last_fun := cld_mrToLastJS h true eol_backn quotel_backdouble (fst (mrl.(cld_mr_last))) in
      let cld_eff_params := cld_mrParamsLast rulename (snd (mrl.(cld_mr_last))) in
      mapReduceStringstoDesignDocs mrpl last_fun cld_eff_params rulename.

    Definition mapReducePairstoJSMRCloudant (h:list (string*string)) (mrl : cld_mrl) : string :=
      let mrpl := cld_mrToJS h false eol_newline quotel_double mrl in
      mapReduceStringstoJS eol_newline mrpl.

  End CloudantJS.
  
End CloudantMRtoJavascript.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
