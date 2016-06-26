/*
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
 */

import java.io.File;
import java.io.FileReader;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.qcert.calib.CACoEngine;
import org.qcert.calib.CALibWrapper.nraenv;


public class JAPITest {
	
    private static void usage() {
	System.err.println("JAPITest expects no arguments\n");
    }

    public static void main(String[] args) throws Exception {
	if(args.length != 0) {
	    usage();
	}
	// Get a caco engine
	CACoEngine cacoengine = new CACoEngine();

	final String rule = "Example R01 :=  rule_when (\"c\" INSTANCEOF [\"entities.Customer\"] WHERE (passert (pbinop AEq (pbdot \"age\" (pit)) (#` 32))));;  rule_return (pbinop ASConcat (toString (#` \"Customer =\")) (toString (pletIt ((lookup \"c\")) (pbdot \"name\" (pit))))).";

        nraenv n = cacoengine.rule_to_nraenv(rule);
	// May need -Xss ...
	// String pretty_nra = cacoengine.pretty_nraenv(false,120,n);
	// System.out.println("The *Unoptimizedd* NRAEnv for rule:\n\n" + rule + "\n\nis:\n\n" + pretty_nra);
	// 
	// String pretty_nra_opt = cacoengine.pretty_nraenv(false,120,cacoengine.optimize_nraenv(n));
	// System.out.println("The *Optimized* NRAEnv for rule:\n\n" + rule + "\n\nis:\n\n" + pretty_nra_opt);
	// 
	// String pretty_nnrc = cacoengine.pretty_nnrc(false,120,cacoengine.nraenv_to_nnrc(n));
	// System.out.println("The NNRC for rule:\n\n" + rule + "\n\nis:\n\n" + pretty_nnrc);

	String result_js = cacoengine.nraenv_to_js(n);
	System.out.println("The JS for rule:\n\n" + rule + "\n\nis:\n\n" + result_js);

	String result_spark = cacoengine.nraenv_to_spark("R01",n);
	System.out.println("The Spark for rule:\n\n" + rule + "\n\nis:\n\n" + result_spark);

	String result_cloudant = cacoengine.nraenv_to_cloudant("[HARNESS]", "toto_", "R01",n);
	System.out.println("The Cloudant design document for rule:\n\n" + rule + "\n\nis:\n\n" + result_cloudant);

	String result_java = cacoengine.nraenv_to_java("Class01", "", n);
	System.out.println("The Java for rule:\n\n" + rule + "\n\nis:\n\n" + result_java);

	final String oql = "select p from p in Person";
	nraenv n2 = cacoengine.oql_to_nraenv(oql);
	String result_js2 = cacoengine.nraenv_to_js(n2);
	System.out.println("The JS for oql:\n\n" + oql + "\n\nis:\n\n" + result_js2);

    }
}
