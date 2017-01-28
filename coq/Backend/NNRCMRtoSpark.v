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
Require Import EquivDec.

Require Import Utils BasicRuntime.
Require Import NNRCRuntime NNRCMRRuntime.
Require Import NNRCtoJavascript.
Require Import ForeignToJavascript ForeignToSpark.
Require Import NNRCMR.

Local Open Scope string_scope.

Section NNRCMRtoSpark.

  Context {fruntime:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftojavascript:foreign_to_javascript}.
  Context {ftospark:foreign_to_spark}.

  Definition js_endl := eol_backn.

    Section sanitize.
      Require Import NNRCtoJavascript.
      Import ListNotations.
      Require Import Ascii String.
      
      Definition scalaAllowedIdentifierInitialCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%char.

  (* javascript identifiers can have (after the first character), a unicode letter, digit, underscore, or dollar sign.
         Since Coq does not seem to have a unicode library, we just
         allow ascii characters,
   *)
      Definition scalaAllowedIdentifierCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_"]%char.

      Definition scalaIdentifierInitialCharacterToAdd := "X"%char.
      Definition scalaIdenitiferCharacterForReplacement := "X"%char.

      Definition scalaIdentifierFixInitial (ident:string) : string
        := match ident with
           (* We also don't want empty identifier names *)
           | EmptyString =>
             String scalaIdentifierInitialCharacterToAdd EmptyString
           | String a _ =>
             if in_dec ascii_dec a scalaAllowedIdentifierInitialCharacters
             then ident
             else String scalaIdentifierInitialCharacterToAdd ident
           end.

      Definition scalaIdentifierSanitizeChar (a:ascii)
        := if a == "$"%char (* special case for readability *)
           then "_"%char
           else if in_dec ascii_dec a scalaAllowedIdentifierCharacters
                then a
                else scalaIdenitiferCharacterForReplacement.

  Definition scalaIdentifierSanitizeBody (ident:string)
    := map_string scalaIdentifierSanitizeChar ident.
  
  Definition scalaIdentifierSanitize (ident:string)
    := scalaIdentifierFixInitial (scalaIdentifierSanitizeBody ident).

  Definition scalaSafeSeparator := "_".

  (* pulled of off various lists of javascript reserved keywords 
         as well some common html/java words that should be avoided
          in case of shared context/interop *)
  Definition scalaAvoidList :=
    ["abstract"; "case"; "catch"; "class"; "def"; "do" ; "else"; "extends"
     ; "false"; "final"; "finally"; "for"; "forSome"; "if" ; "implicit"; "import"
     ; "lazy"; "match"; "new"; "null"; "object"; "override"
     ; "package"; "private"; "protected"; "return"; "sealed"; "super";
       "this"; "throw"; "trait"; "try"; "true"; "type"; "val"; "var"
       ; "while"; "with"; "yield"].

  Definition nnrcmr_rename_local_for_js (mrl:nnrcmr)
    := nnrcmr_rename_local
         jsSafeSeparator
         jsIdentifierSanitize
         jsAvoidList
         mrl.
  
  Definition nnrcmr_rename_graph_for_scala (mrl:nnrcmr)
    := nnrcmr_rename_graph
         scalaSafeSeparator
         scalaIdentifierSanitize
         scalaAvoidList 
         mrl.

  Definition nnrcmr_rename_for_spark (mrl:nnrcmr)
    := nnrcmr_rename_graph_for_scala
         (nnrcmr_rename_local_for_js mrl).

    End sanitize.
    
  Section MRSpark.

    Definition rdd_env_id (x: string) :=
      "RDD"++(scalaIdentifierSanitize x).

    Definition rdd_map_id (x: string) :=
      "RDDMap_"++(scalaIdentifierSanitize x).

    Definition rdd_reduce_id (x: string) :=
      "RDDReduce_"++(scalaIdentifierSanitize x).

    Definition attr_id (x: string) :=
      "'"++x++"'".

    (* Definition get_engine_func (scala_endl:string) := *)
    (*   "var engine : Option[javax.script.ScriptEngine] = None" ++ scala_endl ++ *)
    (*   "def get_engine() : javax.script.ScriptEngine = {" ++ scala_endl ++ *)
    (*   "  if (engine == None) {" ++ scala_endl ++ *)
    (*   "    val factory = new javax.script.ScriptEngineManager" ++ scala_endl ++ *)
    (*   "    val new_engine = factory.getEngineByName(""JavaScript"")" ++ scala_endl ++ *)
    (*   "    load_harness(new_engine)" ++ scala_endl ++ *)
    (*   "    engine = Some (new_engine)" ++ scala_endl ++ *)
    (*   "  }" ++ scala_endl ++ *)
    (*   "  return engine.get" ++ scala_endl ++ *)
    (*   "}" ++ scala_endl. *)

    Definition get_engine_func (scala_endl:string) :=
      "var engine : Option[javax.script.ScriptEngine] = None" ++ scala_endl ++
      "def get_engine() : javax.script.ScriptEngine = {" ++ scala_endl ++
      "  val factory = new javax.script.ScriptEngineManager" ++ scala_endl ++
      "  val new_engine = factory.getEngineByName(""JavaScript"")" ++ scala_endl ++
      "  load_harness(new_engine)" ++ scala_endl ++
      "  return (new_engine)" ++ scala_endl ++
      "}" ++ scala_endl.

    Definition array_of_js_func_v7 (scala_endl:string) :=
      "def array_of_js(e: javax.script.ScriptEngine, js_arr: Object): Array[String] = {" ++ scala_endl ++
      "  e.put(""js_arr"", js_arr)" ++ scala_endl ++
      "  val jarr = e.eval(""js_arr.map(function(elem){ return JSON.stringify(elem); })"").asInstanceOf[jdk.nashorn.api.scripting.ScriptObjectMirror].to(classOf[jdk.nashorn.internal.runtime.ScriptObject])" ++ scala_endl ++
      "  val arr = jarr.getArray().asObjectArray()" ++ scala_endl ++
      "  val sarr = arr.map(_.toString())" ++ scala_endl ++
      "  return sarr" ++ scala_endl ++
      "}" ++ scala_endl.

    Definition array_of_js_func_v8 (scala_endl:string) :=
      "def array_of_js(e: javax.script.ScriptEngine, js_arr: Object): Array[String] = {" ++ scala_endl ++
      "  e.put(""js_arr"", js_arr)" ++ scala_endl ++
      "  val jarr = e.eval(""js_arr.map(function(elem){ return JSON.stringify(elem); })"").asInstanceOf[jdk.nashorn.api.scripting.ScriptObjectMirror].to(classOf[jdk.nashorn.internal.runtime.ScriptObject])" ++ scala_endl ++
      "  val arr = jarr.getArray().asObjectArray()" ++ scala_endl ++
      "  val sarr = arr.map(_.toString())" ++ scala_endl ++
      "  return sarr" ++ scala_endl ++
      "}" ++ scala_endl.

    Definition array_of_js_func := array_of_js_func_v8.

    (* Definition array_of_js_func (scala_endl:string) := *)
    (*   "def array_of_js(js_arr: Object): Array[String] = {" ++ scala_endl ++ *)
    (*   "  val e = get_engine()" ++ scala_endl ++ *)
    (*   "  e.put(""js_arr"", js_arr)" ++ scala_endl ++ *)
    (*   "  val arr = e.eval(""if (typeof map_1 === 'undefined') {\n""+" ++ scala_endl ++ *)
    (*   "		   ""  function to_java(arr) {\n""+" ++ scala_endl ++ *)
    (*   "		   ""      var res = java.lang.reflect.Array.newInstance(String, arr.length);\n""+" ++ scala_endl ++ *)
    (*   "		   ""    for (var i = 0; i < arr.length; i++) {\n""+" ++ scala_endl ++ *)
    (*   "		   ""      res[i] = JSON.stringify(arr[i]);\n""+" ++ scala_endl ++ *)
    (*   "		   ""    }\n""+" ++ scala_endl ++ *)
    (*   "		   ""    return res;\n""+" ++ scala_endl ++ *)
    (*   "		   ""  }\n""+" ++ scala_endl ++ *)
    (*   "		   ""}\n""+" ++ scala_endl ++ *)
    (*   "		   ""to_java(js_arr)"")" ++ scala_endl ++ *)
    (*   "  return arr.asInstanceOf[Array[String]]" ++ scala_endl ++ *)
    (*   "}" ++ scala_endl. *)

    Definition js_of_iterable_func (scala_endl:string) :=
      "def js_of_iterable(coll: Iterable[String]): String = {" ++ scala_endl ++
      "  /* Hack! */" ++ scala_endl ++
      "  var values = ""[ """ ++ scala_endl ++
      "  var first = true" ++ scala_endl ++
      "  for (elem <- coll) {" ++ scala_endl ++
      "    if (!first) {" ++ scala_endl ++
      "      values = values + "", """ ++ scala_endl ++
      "    }" ++ scala_endl ++
      "    values = values + elem" ++ scala_endl ++
      "    first = false" ++ scala_endl ++
      "  }" ++ scala_endl ++
      "  values = values + "" ]""" ++ scala_endl ++
      "  values" ++ scala_endl ++
      "}" ++ scala_endl.


    Definition load_harness_from_file_func (scala_endl:string) (quotel:string) :=
      "def load_harness(e:javax.script.ScriptEngine) {" ++ scala_endl ++
      "  e.eval(new java.io.FileReader(dataFile))" ++ scala_endl ++
      "  e.eval(new java.io.FileReader(harnessFile))" ++ scala_endl ++
      "}" ++ scala_endl.

    Definition load_env_defs (init: string) (scala_endl:string) (quotel:string) :=
      "def mkWorld(e: javax.script.ScriptEngine) : Object = {" ++ scala_endl ++
      "  /* XXX Should be updated to use the new io format XXX */" ++ scala_endl ++
      "  e.eval(new java.io.FileReader(dataFile))" ++ scala_endl ++
      "  e.eval(""var world = mkWorld(input)"")" ++ scala_endl ++
      "  e.eval(""world["++(attr_id init)++"] = null"")" ++ scala_endl ++
      "  e.eval(""world"")" ++ scala_endl ++
      "}" ++ scala_endl ++
      "def loadScalar(e: javax.script.ScriptEngine, sc: SparkContext, world: Object, attr: String) : org.apache.spark.rdd.RDD[String] = {" ++ scala_endl ++
      "  e.put(""world"", world)" ++ scala_endl ++
      "  val coll = array_of_js(e, e.eval(""[ world[""+attr+""] ]""))" ++ scala_endl ++
      "  sc.parallelize(coll)" ++ scala_endl ++
      "}" ++ scala_endl ++
      "def loadDistributed(e: javax.script.ScriptEngine, sc: SparkContext, world: Object, attr: String): org.apache.spark.rdd.RDD[String] = {" ++ scala_endl ++
      "  e.put(""world"", world)" ++ scala_endl ++
      "  val coll = array_of_js(e, e.eval(""world[""+attr+""]""))" ++ scala_endl ++
      "  sc.parallelize(coll)" ++ scala_endl ++
      "}" ++ scala_endl.


    Lemma var_loc_eq_dec:
      forall x_loc y_loc : (var * dlocalization),
        { x_loc = y_loc } + { x_loc <> y_loc }.
    Proof.
      intros.
      destruct x_loc as [ x loc1 ]; simpl.
      destruct y_loc as [ y loc2 ]; simpl.
      apply pair_eq_dec.
      - apply string_dec.
      - apply dlocalization_eq_dec.
    Qed.

    Definition load_env (env_vars: list (var * dlocalization)) (scala_endl:string) (quotel:string) :=
      let env_vars := List.nodup var_loc_eq_dec env_vars in
      "val e = get_engine()" ++ scala_endl ++
      "val world = mkWorld(e)" ++ scala_endl ++
      List.fold_left
        (fun acc (x_loc: var * dlocalization) =>
           let (x, loc) := x_loc in
           let unconsted_x := unConstVar x in (* Removes CONST$ prefix added during compilation for consistency with external specification *)
           let load_func :=
               match loc with
               | Vlocal => "loadScalar"
               | Vdistr => "loadDistributed"
               end
           in
           acc ++
           "val "++(rdd_env_id x)++" = "++load_func++"(e, sc, world, """++(attr_id unconsted_x)++""")" ++ scala_endl)
        env_vars "".

    Definition check_result_from_file_func (scala_endl:string) (quotel:string) :=
      "def check_result(actual: String) {" ++ scala_endl ++
      "  val factory = new javax.script.ScriptEngineManager" ++ scala_endl ++
      "  val e = factory.getEngineByName(""JavaScript"")" ++ scala_endl ++
      "  load_harness(e)" ++ scala_endl ++
      "  e.eval(""var actual = ""+actual+"";"")" ++ scala_endl ++
      "  e.eval(""var expected = [[output]];"")" ++ scala_endl ++
      "  e.eval(""if (equal(expected, actual)) { print(\""OK\\n\""); } else { print(\""ERROR\\n\""); }"");" ++ scala_endl ++
      "}" ++ scala_endl.

    (**
      If the map-reduce has the identifier [id], the argument name
      [x] and body [n], we want to generate the following Scala code
      for MapFlatten:

        val RDDMap_id = RDD_input.flatMap(x => {
          val e = get_engine()
          val x_js = e.eval(x.asInstanceOf[String])
          e.put("x", x_js)
          array_of_js(e, e.eval("if (typeof map_id === 'undefined') {"+
            "function map_id(x) {"+
              "js(n)"+
            "}"
          "}"
          "map_id(x)"))
        })

     *)
    Definition scala_of_mr_map (mr_id: string) (input: string) (mr_map: map_fun) (scala_endl:string) (quotel:string) :=
      match mr_map with
      | MapDist (map_v, map_f) =>
        let map_v_js := "map_arg" in  (* Waring: we suppose that map_f does not capture "map_arg". *)
        let '(j, v, t) := nnrcToJSunshadow map_f 3 1 js_endl quotel (map_v::nil) ((map_v, map_v_js)::nil) in
          "val "++(rdd_map_id mr_id)++" = "++(rdd_env_id input)++".map(x => {" ++ scala_endl ++
        "  val e = get_engine()" ++ scala_endl ++
        "  val x_js = e.eval(""var tmp = ""+x.asInstanceOf[String]+""; tmp"")" ++ scala_endl ++
        "  e.put(""x"", x_js)" ++ scala_endl ++
        "  e.eval(""if (typeof map_"++(mr_id)++" === 'undefined') {"++js_endl++"""+" ++ scala_endl ++
        "         ""  function map_"++(mr_id)++"("++map_v_js++") {"++js_endl++"""+"++ scala_endl ++
        "         """++j++js_endl++"""+" ++ scala_endl ++
        "         ""    return "++v++";"++js_endl++"""+" ++ scala_endl ++
        "         ""  }"++js_endl++"""+" ++ scala_endl ++
        "         ""}"++js_endl++"""+" ++ scala_endl ++
        "         ""JSON.stringify(map_"++(mr_id)++"(x))"").asInstanceOf[String]" ++ scala_endl ++
        "})" ++ scala_endl
      | MapDistFlatten (map_v, map_f) =>
        let map_v_js := "map_arg" in  (* Waring: we suppose that map_f does not capture "map_arg". *)
        let '(j, v, t) := nnrcToJSunshadow map_f 3 1 js_endl quotel (map_v::nil) ((map_v, map_v_js)::nil) in
          "val "++(rdd_map_id mr_id)++" = "++(rdd_env_id input)++".flatMap(x => {" ++ scala_endl ++
        "  val e = get_engine()" ++ scala_endl ++
        "  val x_js = e.eval(""var tmp = ""+x.asInstanceOf[String]+""; tmp"")" ++ scala_endl ++
        "  e.put(""x"", x_js)" ++ scala_endl ++
        "  array_of_js(e, e.eval(""if (typeof map_"++(mr_id)++" === 'undefined') {"++js_endl++"""+" ++ scala_endl ++
        "         ""  function map_"++(mr_id)++"("++map_v_js++") {"++js_endl++"""+"++ scala_endl ++
        "         """++j++js_endl++"""+" ++ scala_endl ++
        "         ""    return "++v++";"++js_endl++"""+" ++ scala_endl ++
        "         ""  }"++js_endl++"""+" ++ scala_endl ++
        "         ""}"++js_endl++"""+" ++ scala_endl ++
        "         ""map_"++(mr_id)++"(x)""))" ++ scala_endl ++
        "})" ++ scala_endl
      | MapScalar (map_v, map_f) => (* XXX TODO: change when scalar values are going tobe implemented as scalar *)
        let map_v_js := "map_arg" in  (* Waring: we suppose that map_f does not capture "map_arg". *)
        let '(j, v, t) := nnrcToJSunshadow map_f 3 1 js_endl quotel (map_v::nil) ((map_v, map_v_js)::nil) in
          "val "++(rdd_map_id mr_id)++" = "++(rdd_env_id input)++".flatMap(x => {" ++ scala_endl ++
        "  val e = get_engine()" ++ scala_endl ++
        "  val x_js = e.eval(""var tmp = ""+x.asInstanceOf[String]+""; tmp"")" ++ scala_endl ++
        "  e.put(""x"", x_js)" ++ scala_endl ++
        "  array_of_js(e, e.eval(""if (typeof map_"++(mr_id)++" === 'undefined') {"++js_endl++"""+" ++ scala_endl ++
        "         ""  function map_"++(mr_id)++"("++map_v_js++") {"++js_endl++"""+"++ scala_endl ++
        "         """++j++js_endl++"""+" ++ scala_endl ++
        "         ""    return "++v++";"++js_endl++"""+" ++ scala_endl ++
        "         ""  }"++js_endl++"""+" ++ scala_endl ++
        "         ""}"++js_endl++"""+" ++ scala_endl ++
        "         ""map_"++(mr_id)++"(x)""))" ++ scala_endl ++
        "})" ++ scala_endl
      end.

    (** functions to compute stats *)
    Definition stats_funcs scala_endl :=
      "def statsReduce (x: String, y: String): String = {" ++ scala_endl ++
      "  val e = get_engine()" ++ scala_endl ++
      "  var res:String = """"" ++ scala_endl ++
      "  if (x.equals("""")) {" ++ scala_endl ++
      "    val y_js = e.eval(""var tmp = ""+y+""; tmp"")" ++ scala_endl ++
      "    e.put(""y"", y_js)" ++ scala_endl ++
      "    res = e.eval(""var res = { 'count': 1, 'sum': y, 'min': y, 'max': y };"++js_endl++"""+" ++ scala_endl ++
      "                 ""JSON.stringify(res)"").asInstanceOf[String]" ++ scala_endl ++
      "  } else {" ++ scala_endl ++
      "    val x_js = e.eval(""var tmp = ""+x+""; tmp"")" ++ scala_endl ++
      "    e.put(""x"", x_js)" ++ scala_endl ++
      "    val y_js = e.eval(""var tmp = ""+y+""; tmp"")" ++ scala_endl ++
      "    e.put(""y"", y_js)" ++ scala_endl ++
      "    res = e.eval(""var res = { 'count': x['count'] + 1,"++js_endl++"""+" ++ scala_endl ++
      "                 ""            'sum': x['sum'] + y,"++js_endl++"""+" ++ scala_endl ++
      "                 ""            'min': Math.min(x['min'], y),"++js_endl++"""+" ++ scala_endl ++
      "                 ""            'max': Math.max(x['max'], y) };"++js_endl++"""+" ++ scala_endl ++
      "                 ""JSON.stringify(res)"").asInstanceOf[String]" ++ scala_endl ++
      "  }" ++ scala_endl ++
      "  return res" ++ scala_endl ++
      "}" ++ scala_endl ++
      "def statsRereduce (x: String, y: String): String = {" ++ scala_endl ++
      "  val e = get_engine()" ++ scala_endl ++
      "  var res:String = """"" ++ scala_endl ++
      "  if (x.equals("""")) {" ++ scala_endl ++
      "    if (y.equals("""")) {" ++ scala_endl ++
      "      res = ""{ 'count': 0, 'sum': 0, 'min': 0, 'max': 0 }""" ++ scala_endl ++
      "    } else {" ++ scala_endl ++
      "      res = y" ++ scala_endl ++
      "    }" ++ scala_endl ++
      "  } else {" ++ scala_endl ++
      "    if (y.equals("""")) {" ++ scala_endl ++
      "      res = x" ++ scala_endl ++
      "    } else {" ++ scala_endl ++
      "      val x_js = e.eval(""var tmp = ""+x+""; tmp"")" ++ scala_endl ++
      "      e.put(""x"", x_js)" ++ scala_endl ++
      "      val y_js = e.eval(""var tmp = ""+y+""; tmp"")" ++ scala_endl ++
      "      e.put(""y"", y_js)" ++ scala_endl ++
      "      res = e.eval(""var res = { 'count': x['count'] + y['count'],"++js_endl++"""+" ++ scala_endl ++
      "                   ""            'sum': x['sum'] + y['sum'],"++js_endl++"""+" ++ scala_endl ++
      "                   ""            'min': Math.min(x['min'], y['min']),"++js_endl++"""+" ++ scala_endl ++
      "                   ""            'max': Math.max(x['max'], y['max']) };"++js_endl++"""+" ++ scala_endl ++
      "                   ""JSON.stringify(res)"").asInstanceOf[String]" ++ scala_endl ++
      "    }" ++ scala_endl ++
      "  }" ++ scala_endl ++
      "  return res" ++ scala_endl ++
      "}" ++ scala_endl.

    (**
        Case Flatten:
          val RDDReduce_id = RDDMap_id

        Case Collect:
          val RDDReduce_id = (() => {
            val e = get_engine()
            val values = RDDMap_id.collect()
            val values_js = e.eval("var tmp = "+(js_of_iterable(values))+"; tmp")
            e.put("values", values_js)
            val res = e.eval("if (typeof reduce_id === 'undefined') {"+
          		   "  function reduce_id(red_arg) { red_body; return v }"+
          		   "}"+
          		   "JSON.stringify(reduce_id(values))")
            sc.parallelize(Array(res))
          }: org.apache.spark.rdd.RDD[Object]) ()

     *)
    Definition scala_of_mr_reduce (mr_id: string) (mr_reduce: reduce_fun) (scala_endl:string) (quotel:string) :=
      match mr_reduce with
      | RedId =>
        "var "++(rdd_reduce_id mr_id)++" = "++(rdd_map_id mr_id) ++ scala_endl
      | RedCollect reduce =>
        let (red_values_v, red_f) := reduce in
        let red_values_v_js := "values" in
        let '(j, v, t) := nnrcToJSunshadow red_f 1 1 js_endl quotel (red_values_v :: nil) ((red_values_v, red_values_v_js)::nil) in
        "val "++(rdd_reduce_id mr_id)++" = (() => {" ++ scala_endl ++
        "  val e = get_engine()" ++ scala_endl ++
        "  val values = "++(rdd_map_id mr_id)++".collect()" ++ scala_endl ++
        "  val values_js = e.eval(""var tmp = ""+(js_of_iterable(values))+""; tmp"")" ++ scala_endl ++
        "  e.put(""values"", values_js)" ++ scala_endl ++
        "  val res = e.eval(""if (typeof reduce_"++(mr_id)++" === 'undefined') {""+" ++ scala_endl ++
        "		   ""  function reduce_"++(mr_id)++"("++red_values_v_js++") {"++js_endl++"""+"++ scala_endl ++
        "            """++j++js_endl++"""+" ++ scala_endl ++
        "            ""    return "++v++";"++js_endl++"""+" ++ scala_endl ++
        "            ""  }""+" ++ scala_endl ++
        "		   ""}""+" ++ scala_endl ++
        "		   ""JSON.stringify(reduce_"++(mr_id)++"(values))"").asInstanceOf[String]" ++ scala_endl ++
        "  sc.parallelize(Array(res))" ++ scala_endl ++
        "}: org.apache.spark.rdd.RDD[String]) ()" ++ scala_endl
      | RedOp rop =>
        match rop with
          | RedOpForeign frop =>
            "val "++(rdd_reduce_id mr_id)++" = (() => {" ++ scala_endl ++
                  "  val res = "++(rdd_map_id mr_id) ++ (foreign_to_spark_reduce_op frop scala_endl quotel) ++ scala_endl ++
                  "  sc.parallelize(Array(res))" ++ scala_endl ++
                  "}: org.apache.spark.rdd.RDD[String]) ()" ++ scala_endl
        end
      | RedSingleton =>
        "val "++(rdd_reduce_id mr_id)++" = "++(rdd_map_id mr_id) ++ scala_endl
      end.

    (**

    *)
    Definition scala_of_mr (mr_id: string) (mr: mr) (outputs: list var) (scala_endl:string) (quotel:string) :=
      scala_of_mr_map mr_id mr.(mr_input) mr.(mr_map) scala_endl quotel ++
      scala_of_mr_reduce mr_id mr.(mr_reduce) scala_endl quotel ++
      if in_dec equiv_dec mr.(mr_output) outputs then
        (rdd_env_id mr.(mr_output))++" = "++(rdd_env_id mr.(mr_output))++"++"++(rdd_reduce_id mr_id)
      else
        "var "++(rdd_env_id mr.(mr_output))++" = "++(rdd_reduce_id mr_id).

    Definition scala_of_mr_chain (l:list mr) (scala_endl:string) (quotel:string) :=
      let '(_, _, scala) :=
          List.fold_left
            (fun (acc: string * list var * string) mr =>
               let '(mr_id, outputs, s) := acc in
               let mr_scala := scala_of_mr mr_id mr outputs scala_endl quotel in
               ((append mr_id "_next"), mr.(mr_output)::outputs, s++scala_endl++mr_scala))
            l ("something_", nil, "")
      in
      scala ++ scala_endl.

    Fixpoint string_of_list sep l :=
      match l with
      | nil => ""
      | s::nil => s
      | s::l => s++sep++(string_of_list sep l)
      end.

    Definition scala_of_mr_last (mr_last: ((list var * nnrc) * list (var * dlocalization))) (scala_endl:string) (quotel:string) :=
      (* We suppose that this code is put into a context where there is a JavaScript engine e *)
      let params_js :=
          List.map (fun x => "v"++x) (fst (fst mr_last))
      in
      let args_js :=
          List.map
            (fun x_loc =>
               match x_loc with
               | (x, Vlocal) => """+"++(rdd_env_id x)++".collect()(0)"++"+"""
               | (x, Vdistr) => """+"++(rdd_env_id x)++".collect()"++"+"""
               end)
            (snd mr_last)
      in
      let result :=
          let '(j, v, _) := nnrcToJSunshadow (snd (fst mr_last)) 3 1 js_endl quotel nil nil in
          "e.eval(""(function ("++(string_of_list ", " params_js)++"){"++js_endl++"""+"++ scala_endl ++
          "       """++j++js_endl++"""+" ++ scala_endl ++
          "       ""    return JSON.stringify("++v++");"++js_endl++"""+" ++ scala_endl ++
          "       ""})("++(string_of_list ", " args_js)++")"").asInstanceOf[String]"++ scala_endl
      in
      result.

    Definition scala_of_nnrcmr (mrl:nnrcmr) (scala_endl:string) (quotel:string) :=
      scala_of_mr_chain mrl.(mr_chain) scala_endl quotel ++
      scala_of_mr_last mrl.(mr_last) scala_endl quotel.

    Definition nnrcmrToSparkTopDataFromFile (test_name: string) (init: var) (l:nnrcmr) (scala_endl:string) (quotel: string) :=
      "import org.apache.spark.SparkContext" ++ scala_endl ++
      "import org.apache.spark.SparkContext._" ++ scala_endl ++
      "import org.apache.spark.SparkConf" ++ scala_endl ++
      "import java.io._" ++ scala_endl ++
      scala_endl ++
      "object "++test_name++" {" ++ scala_endl ++
      scala_endl ++
      "var harnessFile: String = """"" ++ scala_endl ++
      "var dataFile: String = """"" ++ scala_endl ++
      get_engine_func scala_endl ++
      scala_endl ++
      js_of_iterable_func scala_endl ++
      scala_endl ++
      array_of_js_func scala_endl ++
      scala_endl ++
      stats_funcs scala_endl ++
      scala_endl ++
      load_harness_from_file_func scala_endl quotel ++ scala_endl ++
      scala_endl ++
      load_env_defs init scala_endl quotel ++
      scala_endl ++
      check_result_from_file_func scala_endl quotel ++
      scala_endl ++
      "def run(sc: SparkContext): String = {" ++ scala_endl ++
      get_engine_func scala_endl ++ scala_endl ++
      load_env l.(mr_inputs_loc) scala_endl quotel ++ scala_endl ++
      scala_of_nnrcmr l scala_endl quotel ++
      "}" ++ scala_endl ++
      scala_endl ++
      "def main(args: Array[String]) {" ++ scala_endl ++
      "  if (args.length != 2 && args.length != 3) {" ++ scala_endl ++
      "    println(""Expected arguments: harness.js, test.js.io [and output.io]"")" ++ scala_endl ++
      "    sys.exit(1)" ++ scala_endl ++
      "  }" ++ scala_endl ++
      "  harnessFile = args(0)" ++ scala_endl ++
      "  dataFile = args(1)" ++ scala_endl ++
      "  val conf = new SparkConf().setAppName("""++test_name++""")" ++ scala_endl ++
      "  val sc = new SparkContext(conf)" ++ scala_endl ++
      "  val json_result = run(sc)" ++ scala_endl ++
      "  if (args.length == 3) {" ++ scala_endl ++
      "    val pw = new PrintWriter(new File(args(2)))" ++ scala_endl ++
      "    pw.write(json_result)" ++ scala_endl ++
      "    pw.close" ++ scala_endl ++
      "  }" ++ scala_endl ++
      "  println(json_result)" ++ scala_endl ++
      "  if (args.length ==2)" ++ scala_endl ++
      "    check_result(json_result)"  ++ scala_endl ++
      "}" ++ scala_endl ++
      "}" ++ scala_endl.


  End MRSpark.

  Definition nnrcmrToSparkTopDataFromFileTop (test_name: string) (init: var) (l:nnrcmr) : string :=
    nnrcmrToSparkTopDataFromFile test_name init l eol_newline "'".

End NNRCMRtoSpark.

(*
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
