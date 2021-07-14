(*
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

(** Imp with the Json data model *)

Require Import String.
Require Import List.
Require Import ZArith.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignEJson.
Require Import EJson.
Require Import EJsonGroupBy.
Require Import EJsonSortBy.
Require Import ForeignEJsonRuntime.

Section EJsonRuntimeOperators.
  Local Open Scope string.

  Context {fejson:foreign_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.

  Section Syntax.
    Inductive ejson_runtime_op :=
    (* Generic *)
    | EJsonRuntimeEqual : ejson_runtime_op
    | EJsonRuntimeCompare : ejson_runtime_op
    | EJsonRuntimeToString : ejson_runtime_op
    | EJsonRuntimeToText : ejson_runtime_op
    (* Record *)
    | EJsonRuntimeRecConcat : ejson_runtime_op
    | EJsonRuntimeRecMerge : ejson_runtime_op
    | EJsonRuntimeRecRemove: ejson_runtime_op
    | EJsonRuntimeRecProject: ejson_runtime_op
    | EJsonRuntimeRecDot : ejson_runtime_op
    (* Array *)
    | EJsonRuntimeArray : ejson_runtime_op
    | EJsonRuntimeArrayLength : ejson_runtime_op
    | EJsonRuntimeArrayPush : ejson_runtime_op
    | EJsonRuntimeArrayAccess : ejson_runtime_op
    (* Sum *)
    | EJsonRuntimeEither : ejson_runtime_op
    | EJsonRuntimeToLeft: ejson_runtime_op
    | EJsonRuntimeToRight: ejson_runtime_op
    (* Brand *)
    | EJsonRuntimeBrand : ejson_runtime_op
    | EJsonRuntimeUnbrand : ejson_runtime_op
    | EJsonRuntimeCast : ejson_runtime_op
    (* Collection *)
    | EJsonRuntimeDistinct : ejson_runtime_op
    | EJsonRuntimeSingleton : ejson_runtime_op
    | EJsonRuntimeFlatten : ejson_runtime_op
    | EJsonRuntimeUnion : ejson_runtime_op
    | EJsonRuntimeMinus : ejson_runtime_op
    | EJsonRuntimeMin : ejson_runtime_op
    | EJsonRuntimeMax : ejson_runtime_op
    | EJsonRuntimeNth : ejson_runtime_op
    | EJsonRuntimeCount : ejson_runtime_op
    | EJsonRuntimeContains : ejson_runtime_op
    | EJsonRuntimeSort : ejson_runtime_op
    | EJsonRuntimeGroupBy : ejson_runtime_op
    (* String *)
    | EJsonRuntimeLength : ejson_runtime_op
    | EJsonRuntimeSubstring : ejson_runtime_op
    | EJsonRuntimeSubstringEnd : ejson_runtime_op
    | EJsonRuntimeStringJoin : ejson_runtime_op
    | EJsonRuntimeLike : ejson_runtime_op
    (* Integer *)
    | EJsonRuntimeNatLt : ejson_runtime_op
    | EJsonRuntimeNatLe : ejson_runtime_op
    | EJsonRuntimeNatPlus : ejson_runtime_op
    | EJsonRuntimeNatMinus : ejson_runtime_op
    | EJsonRuntimeNatMult : ejson_runtime_op
    | EJsonRuntimeNatDiv : ejson_runtime_op
    | EJsonRuntimeNatRem : ejson_runtime_op
    | EJsonRuntimeNatAbs : ejson_runtime_op
    | EJsonRuntimeNatLog2 : ejson_runtime_op
    | EJsonRuntimeNatSqrt : ejson_runtime_op
    | EJsonRuntimeNatMinPair : ejson_runtime_op
    | EJsonRuntimeNatMaxPair : ejson_runtime_op
    | EJsonRuntimeNatSum : ejson_runtime_op
    | EJsonRuntimeNatMin : ejson_runtime_op
    | EJsonRuntimeNatMax : ejson_runtime_op
    | EJsonRuntimeNatArithMean : ejson_runtime_op
    | EJsonRuntimeFloatOfNat : ejson_runtime_op
    (* Float *)
    | EJsonRuntimeFloatSum : ejson_runtime_op
    | EJsonRuntimeFloatArithMean : ejson_runtime_op
    | EJsonRuntimeFloatMin : ejson_runtime_op
    | EJsonRuntimeFloatMax : ejson_runtime_op
    | EJsonRuntimeNatOfFloat : ejson_runtime_op
    (* Foreign *)
    | EJsonRuntimeForeign (fop:foreign_ejson_runtime_op) : ejson_runtime_op
    .

  End Syntax.

  Section Util.
    Local Open Scope string.

    Definition string_of_ejson_runtime_op (op: ejson_runtime_op) :=
      match op with
      (* Generic *)
      | EJsonRuntimeEqual => "equal"
      | EJsonRuntimeCompare => "compare"
      | EJsonRuntimeToString => "toString"
      | EJsonRuntimeToText => "toText"
      (* Record *)
      | EJsonRuntimeRecConcat => "recConcat"
      | EJsonRuntimeRecMerge => "recMerge"
      | EJsonRuntimeRecRemove=> "recRemove"
      | EJsonRuntimeRecProject=> "recProject"
      | EJsonRuntimeRecDot => "recDot"
      (* Array *)
      | EJsonRuntimeArray => "array"
      | EJsonRuntimeArrayLength => "arrayLength"
      | EJsonRuntimeArrayPush => "arrayPush"
      | EJsonRuntimeArrayAccess => "arrayAccess"
      (* Sum *)
      | EJsonRuntimeEither => "either"
      | EJsonRuntimeToLeft=> "getLeft"
      | EJsonRuntimeToRight=> "getRight"
      (* Brand *)
      | EJsonRuntimeBrand => "brand"
      | EJsonRuntimeUnbrand => "unbrand"
      | EJsonRuntimeCast => "cast"
      (* Collection *)
      | EJsonRuntimeDistinct => "distinct"
      | EJsonRuntimeSingleton => "singleton"
      | EJsonRuntimeFlatten => "flatten"
      | EJsonRuntimeUnion => "union"
      | EJsonRuntimeMinus => "minus"
      | EJsonRuntimeMin => "min"
      | EJsonRuntimeMax => "max"
      | EJsonRuntimeNth => "nth"
      | EJsonRuntimeCount => "count"
      | EJsonRuntimeContains => "contains"
      | EJsonRuntimeSort => "sort"
      | EJsonRuntimeGroupBy => "groupBy"
      (* String *)
      | EJsonRuntimeLength => "length"
      | EJsonRuntimeSubstring => "substring"
      | EJsonRuntimeSubstringEnd => "substringEnd"
      | EJsonRuntimeStringJoin => "stringJoin"
      | EJsonRuntimeLike => "like"
      (* Integer *)
      | EJsonRuntimeNatLt => "natLt"
      | EJsonRuntimeNatLe => "natLe"
      | EJsonRuntimeNatPlus => "natPlus"
      | EJsonRuntimeNatMinus => "natMinus"
      | EJsonRuntimeNatMult => "natMult"
      | EJsonRuntimeNatDiv => "natDiv"
      | EJsonRuntimeNatRem => "natRem"
      | EJsonRuntimeNatAbs => "natAbs"
      | EJsonRuntimeNatLog2 => "natLog2"
      | EJsonRuntimeNatSqrt => "natSqrt"
      | EJsonRuntimeNatMinPair => "natMinPair"
      | EJsonRuntimeNatMaxPair => "natMaxPair"
      | EJsonRuntimeNatMin => "natMin"
      | EJsonRuntimeNatMax => "natMax"
      | EJsonRuntimeNatSum => "natSum"
      | EJsonRuntimeNatArithMean => "natArithMean"
      | EJsonRuntimeFloatOfNat => "floatOfNat"
      (* Float *)
      | EJsonRuntimeFloatSum => "floatSum"
      | EJsonRuntimeFloatArithMean => "floatArithMean"
      | EJsonRuntimeFloatMin => "floatMin"
      | EJsonRuntimeFloatMax => "floatMax"
      | EJsonRuntimeNatOfFloat => "natOfFloat"
      (* Foreign *)
      | EJsonRuntimeForeign fop => toString fop
      end.

  Fixpoint defaultEJsonToString (j:ejson) : string
    := match j with
       | ejnull => "unit"%string
       | ejbigint n => toString n
       | ejnumber n => toString n
       | ejbool b => toString b
       | ejstring s => stringToString s
       | ejarray l => string_bracket 
                        "["%string
                        (String.concat ", "%string
                                       (map defaultEJsonToString l))
                        "]"%string
       | ejobject ((s1,j')::nil) =>
         if (string_dec s1 "$left") then
           string_bracket
             "Left("%string
             (defaultEJsonToString j')
             ")"%string
         else if (string_dec s1 "$right") then
                string_bracket
                  "Right("%string
                  (defaultEJsonToString j')
                  ")"%string
              else
                string_bracket
                  "{"%string
                  (String.concat ", "%string 
                                 (map (fun xy => let '(x,y):=xy in 
                                                 (append (stringToString (key_decode x)) (append "->"%string
                                                                                                 (defaultEJsonToString y)))
                                      ) ((s1,j')::nil)))
                  "}"%string
      | ejobject ((s1,ejarray j1)::(s2,j2)::nil) =>
        if (string_dec s1 "$class") then
          if (string_dec s2 "$data") then
            match (ejson_brands j1) with
            | Some br =>
              (string_bracket
                 "<"
                 (append (@toString _ ToString_brands br) (append ":" (defaultEJsonToString j2)))
                 ">")
            | None =>
                string_bracket
                  "{"%string
                  (String.concat ", "%string
                                 ((append (stringToString (key_decode s1))
                                          (append "->"%string (string_bracket 
                                                                 "["%string (String.concat ", "%string (map defaultEJsonToString j1)) "]"%string)))
                                    :: (append (stringToString (key_decode s2)) (append "->"%string (defaultEJsonToString j2)))
                                    :: nil))
                  "}"%string
            end
          else
            string_bracket
              "{"%string
              (String.concat ", "%string
                             ((append (stringToString (key_decode s1))
                                      (append "->"%string (string_bracket "["%string (String.concat ", "%string (map defaultEJsonToString j1)) "]"%string)))
                                :: (append (stringToString (key_decode s2)) (append "->"%string (defaultEJsonToString j2)))
                                :: nil))
              "}"%string
        else
          string_bracket
            "{"%string
            (String.concat ", "%string
                           ((append (stringToString (key_decode s1))
                                    (append "->"%string (string_bracket "["%string (String.concat ", "%string (map defaultEJsonToString j1)) "]"%string)))
                              :: (append (stringToString (key_decode s2)) (append "->"%string (defaultEJsonToString j2)))
                              :: nil))
            "}"%string
      | ejobject r =>
        string_bracket
          "{"%string
          (String.concat ", "%string
                         (map (fun xy => let '(x,y):=xy in
                                         (append (stringToString (key_decode x)) (append "->"%string (defaultEJsonToString y)))
                              ) r))
          "}"%string
       | ejforeign fd => toString fd
       end.
    
  End Util.

  Section Evaluation.
    (* XXX We should try and compile the hierarchy in. Currenty it is still used in cast for sub-branding check *)
    Context (h:brand_relation_t).
    Definition ejson_runtime_eval (rt:ejson_runtime_op) (dl:list ejson) : option ejson :=
      match rt with
      (* Generic *)
      | EJsonRuntimeEqual =>
        apply_binary (fun d1 d2 => if ejson_eq_dec d1 d2 then Some (ejbool true) else Some (ejbool false)) dl
      | EJsonRuntimeCompare =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejnumber n1, ejnumber n2 =>
               if float_lt n1 n2
               then
                 Some (ejnumber float_one)
               else if float_gt n1 n2
                    then
                      Some (ejnumber float_neg_one)
                    else
                      Some (ejnumber float_zero)
             | ejbigint n1, ejbigint n2 =>
               if Z_lt_dec n1 n2
               then
                 Some (ejnumber float_one)
               else if Z_gt_dec n1 n2
                    then
                      Some (ejnumber float_neg_one)
                    else
                      Some (ejnumber float_zero)
             | _, _ => None
             end) dl
      | EJsonRuntimeToString =>
        apply_unary
          (fun d =>
             Some (ejstring (foreign_ejson_runtime_tostring d))
          ) dl
      | EJsonRuntimeToText =>
        apply_unary
          (fun d =>
             Some (ejstring (foreign_ejson_runtime_totext d))
          ) dl
      (* Record *)
      | EJsonRuntimeRecConcat =>
        apply_binary
          (fun d1 d2 =>
             match ejson_is_record d1, ejson_is_record d2 with
             | Some r1, Some r2 => Some (ejobject (rec_sort (r1++r2)))
             | _, _ => None
             end) dl
      | EJsonRuntimeRecMerge =>
        apply_binary
          (fun d1 d2 =>
             match ejson_is_record d1, ejson_is_record d2 with
             | Some r1, Some r2 =>
               match @merge_bindings ejson _ ejson_eq_dec r1 r2 with
               | Some x => Some (ejarray ((ejobject x) :: nil))
               | None => Some (ejarray nil)
               end
             | _, _ => None
             end) dl
      | EJsonRuntimeRecRemove =>
        apply_binary
          (fun d1 d2 =>
             match ejson_is_record d1 with
             | Some r =>
               match d2 with
               | ejstring s =>
                 Some (ejobject (rremove r s))
               | _ => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeRecProject =>
        apply_binary
          (fun d1 d2 =>
             match ejson_is_record d1 with
             | Some r =>
               match d2 with
               | ejarray sl =>
                 lift ejobject
                      (lift (rproject r)
                            (of_string_list sl))
               | _ => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeRecDot =>
        apply_binary
          (fun d1 d2 =>
             match ejson_is_record d1 with
             | Some r =>
               match d2 with
               | ejstring s =>
                 edot r s
               | _ => None
               end
             | _ => None
             end) dl
      (* Array *)
      | EJsonRuntimeArray =>
        Some (ejarray dl) (* XXX n-ary *)
      | EJsonRuntimeArrayLength =>
        apply_unary
          (fun d =>
             match d with
             | ejarray ja => Some (ejbigint (Z_of_nat (List.length ja)))
             | _ => None
             end) dl
      | EJsonRuntimeArrayPush =>
        apply_binary
          (fun d1 d2 =>
             match d1 with
             | ejarray ja => Some (ejarray (ja ++ (d2::nil)))
             | _ => None
             end) dl
      | EJsonRuntimeArrayAccess =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejarray ja, ejbigint n =>
               let natish := ZToSignedNat n in
               if (fst natish) then
                 match List.nth_error ja (snd natish) with
                 | None => None
                 | Some d => Some d
                 end
               else None
             | _, _ => None
             end) dl
      (* Sum *)
      | EJsonRuntimeEither =>
        apply_unary
          (fun d =>
             match d with
             | ejobject (("$left", _)::nil) => Some (ejbool true)
             | ejobject (("$right",_)::nil) => Some (ejbool false)
             | _ => None
             end) dl
      | EJsonRuntimeToLeft =>
        apply_unary
          (fun d =>
             match d with
             | ejobject (("$left", d)::nil) => Some d
             | _ => None
             end) dl
      | EJsonRuntimeToRight =>
        apply_unary
          (fun d =>
             match d with
             | ejobject (("$right", d)::nil) => Some d
             | _ => None
             end) dl
      (* Brand *)
      | EJsonRuntimeBrand =>
        apply_binary
          (fun d1 d2 =>
             match d1 with
             | ejarray bls =>
               let ob := of_string_list bls in
               lift (fun b =>
                       ejobject
                         (("$class"%string, ejarray (map ejstring b))
                            ::("$data"%string, d2)
                            ::nil)) ob
             | _ => None
             end
          ) dl
      | EJsonRuntimeUnbrand =>
        apply_unary
          (fun d =>
             match d with
             | ejobject ((s,ejarray jl)::(s',j')::nil) =>
               if (string_dec s "$class") then
                 if (string_dec s' "$data") then
                   match ejson_brands jl with
                   | Some _ => Some j'
                   | None => None
                   end
                 else None
               else None
             | _ => None
             end) dl
      | EJsonRuntimeCast =>
        apply_binary
          (fun d1 d2 : ejson =>
             match d1 with
             | ejarray jl1 =>
               match ejson_brands jl1 with
               | Some b1 =>
                 match d2 with
                 | ejobject ((s,ejarray jl2)::(s',_)::nil) =>
                   if (string_dec s "$class") then
                     if (string_dec s' "$data") then
                       match ejson_brands jl2 with
                       | Some b2 =>
                         if (sub_brands_dec h b2 b1)
                         then
                           Some (ejobject (("$left"%string,d2)::nil))
                         else
                           Some (ejobject (("$right"%string,ejnull)::nil))
                       | None => None
                       end
                     else None
                   else None
                 | _ => None
                 end
               | None => None
               end
             | _ => None
             end) dl

      (* Collection *)
      | EJsonRuntimeDistinct =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               Some (ejarray (@bdistinct ejson ejson_eq_dec l))
             | _ => None
             end)
          dl
      | EJsonRuntimeSingleton =>
        apply_unary
          (fun d =>
             match d with
             | ejarray (d::nil) => Some (ejobject (("$left",d)::nil))
             | ejarray _ => Some (ejobject (("$right",ejnull)::nil))
             | _ => None
             end) dl
      | EJsonRuntimeFlatten =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               lift ejarray (jflatten l)
             | _ => None
             end) dl
      | EJsonRuntimeUnion =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejarray l1, ejarray l2 =>
               Some (ejarray (bunion l1 l2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeMinus =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejarray l1, ejarray l2 =>
               Some (ejarray (bminus l2 l1))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeMin =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejarray l1, ejarray l2 =>
               Some (ejarray (bmin l1 l2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeMax =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejarray l1, ejarray l2 =>
               Some (ejarray (bmax l1 l2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNth =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | (ejarray c), (ejbigint n) =>
               let natish := ZToSignedNat n in
               if (fst natish) then
                 match List.nth_error c (snd natish) with
                 | Some d => Some (ejobject (("$left",d)::nil))
                 | None => Some (ejobject (("$right",ejnull)::nil))
                 end
               else Some (ejobject (("$right",ejnull)::nil))
             | _, _ => None
             end) dl
      | EJsonRuntimeCount =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l => Some (ejbigint (Z_of_nat (bcount l)))
             | _ => None
             end) dl
      | EJsonRuntimeContains =>
        apply_binary
          (fun d1 d2 =>
             match d2 with
             | ejarray l =>
               if in_dec ejson_eq_dec d1 l
               then Some (ejbool true) else Some (ejbool false)
             | _ => None
             end) dl
      | EJsonRuntimeSort =>
        apply_binary
          (fun d1 d2 =>
             match d1 with
             | ejarray l1 =>
               ejson_sort l1 d2
             | _ => None
             end) dl
      | EJsonRuntimeGroupBy =>
        apply_ternary
          (fun d1 d2 d3 =>
             match d3 with
             | ejarray l =>
               match d1 with
               | ejstring g =>
                 match d2 with
                 | ejarray sl =>
                   match of_string_list sl with
                   | Some kl =>
                     lift ejarray (ejson_group_by_nested_eval_table g kl l)
                   | None => None
                   end
                 | _ => None
                 end
               | _ => None
               end
             | _ => None
             end) dl
      (* String *)
      | EJsonRuntimeLength =>
        apply_unary
          (fun d =>
             match d with
             | ejstring s => Some (ejbigint (Z_of_nat (String.length s)))
             | _ => None
             end) dl
      | EJsonRuntimeSubstring =>
        apply_ternary
          (fun d1 d2 d3 =>
             match d1, d2, d3 with
             | ejstring s, ejbigint start, ejbigint len =>              
               let real_start :=
                   (match start with
                    | 0%Z => 0
                    | Z.pos p => Pos.to_nat p
                    | Z.neg n => (String.length s) - (Pos.to_nat n)
                    end) in
               let real_len :=
                   match len with
                   | 0%Z => 0
                   | Z.pos p => Pos.to_nat p
                   | Z.neg n => 0
                   end
               in
               Some (ejstring (substring real_start real_len s))
             | _, _, _ => None
             end) dl
      | EJsonRuntimeSubstringEnd =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejstring s, ejbigint start =>              
               let real_start :=
                   (match start with
                    | 0%Z => 0
                    | Z.pos p => Pos.to_nat p
                    | Z.neg n => (String.length s) - (Pos.to_nat n)
                    end) in
               let real_len := (String.length s) - real_start in
               Some (ejstring (substring real_start real_len s))
             | _, _ => None
             end) dl
      | EJsonRuntimeStringJoin =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejstring sep, ejarray l =>
               match ejson_strings l with
               | Some sl => Some (ejstring (String.concat sep sl))
               | None => None
               end
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeLike =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejstring sreg, ejstring starget =>
               Some (ejbool (string_like starget sreg None))
             | _, _ => None
             end
          ) dl
      (* Integer *)
      | EJsonRuntimeNatLt =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbool (if Z_lt_dec n1 n2 then true else false))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatLe =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbool (if Z_le_dec n1 n2 then true else false))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatPlus =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.add n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatMinus =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.sub n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatMult =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.mul n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatDiv =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.quot n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatRem =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.rem n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatAbs =>
        apply_unary
          (fun d =>
             match d with
             | ejbigint z => Some (ejbigint (Z.abs z))
             | _ => None
             end) dl
      | EJsonRuntimeNatLog2 =>
        apply_unary
          (fun d =>
             match d with
             | ejbigint z => Some (ejbigint (Z.log2 z))
             | _ => None
             end) dl
      | EJsonRuntimeNatSqrt =>
        apply_unary
          (fun d =>
             match d with
             | ejbigint z => Some (ejbigint (Z.sqrt z))
             | _ => None
             end) dl
      | EJsonRuntimeNatMinPair =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.min n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatMaxPair =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | ejbigint n1, ejbigint n2 =>
               Some (ejbigint (Z.max n1 n2))
             | _, _ => None
             end
          ) dl
      | EJsonRuntimeNatSum =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_bigints l with
               | Some zl =>
                 Some (ejbigint (fold_right Zplus 0%Z zl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeNatMin =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_bigints l with
               | Some zl =>
                 Some (ejbigint (bnummin zl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeNatMax =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_bigints l with
               | Some zl =>
                 Some (ejbigint (bnummax zl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeNatArithMean =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               let length := List.length l in
               match ejson_bigints l with
               | Some zl =>
                 Some (ejbigint (Z.quot (fold_right Zplus 0%Z zl) (Z_of_nat length)))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeFloatOfNat =>
        apply_unary
          (fun d =>
             match d with
             | ejbigint n => Some (ejnumber (float_of_int n))
             | _ => None
             end) dl
      (* Float *)
      | EJsonRuntimeFloatSum =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_numbers l with
               | Some nl =>
                 Some (ejnumber (float_list_sum nl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeFloatArithMean =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_numbers l with
               | Some nl =>
                 Some (ejnumber (float_list_arithmean nl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeFloatMin =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_numbers l with
               | Some nl =>
                 Some (ejnumber (float_list_min nl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeFloatMax =>
        apply_unary
          (fun d =>
             match d with
             | ejarray l =>
               match ejson_numbers l with
               | Some nl =>
                 Some (ejnumber (float_list_max nl))
               | None => None
               end
             | _ => None
             end) dl
      | EJsonRuntimeNatOfFloat =>
        apply_unary
          (fun d =>
             match d with
             | ejnumber f => Some (ejbigint (float_truncate f))
             | _ => None
             end) dl
      (* Foreign *)
      | EJsonRuntimeForeign fop =>
        foreign_ejson_runtime_op_interp fop dl
      end.
  End Evaluation.
End EJsonRuntimeOperators.

