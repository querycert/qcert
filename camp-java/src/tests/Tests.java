/**
 * Copyright (C) 2016 Joshua Auerbach 
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
package tests;

import static org.qcert.camp.CampMacros.*;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;
import org.qcert.camp.BridgeToML;
import org.qcert.camp.data.NatData;
import org.qcert.camp.data.StringData;
import org.qcert.camp.pattern.AssertPattern;
import org.qcert.camp.pattern.BinaryOperator;
import org.qcert.camp.pattern.BinaryPattern;
import org.qcert.camp.pattern.CampPattern;
import org.qcert.camp.pattern.ConstPattern;
import org.qcert.camp.pattern.GetConstPattern;
import org.qcert.camp.pattern.LetEnvPattern;
import org.qcert.camp.pattern.LetItPattern;
import org.qcert.camp.pattern.MapPattern;
import org.qcert.camp.pattern.UnaryOperator;
import org.qcert.camp.pattern.UnaryPattern;
import org.qcert.camp.rule.CampRule;
import org.qcert.camp.rule.ReturnRule;
import org.qcert.camp.rule.WhenRule;

/** Various simple tests of AST functionality */ 
public class Tests {
	private static final String test1Raw = 
			"(rule_when (PletEnv (Passert (Pbinop (AEq) (Punop (ADot \"type\" ) (Pit)) (Pconst \"Client\")))" +
			" (PletEnv (Punop (ARec \"C\" ) (Pit)) (Penv))) (rule_when (PletEnv (Passert (PletEnv (Passert (Pbinop (AEq)" +
			" (Punop (ADot \"type\" ) (Pit)) (Pconst \"Marketer\"))) (Pbinop (AContains) (Punop (ADot \"id\" )" +
			" (Punop (ADot \"data\" ) (Punop (ADot \"C\" ) (Penv)))) (Punop (ADot \"clients\" ) (Punop (ADot \"data\" ) (Pit))))))" +
			" (PletEnv (Punop (ARec \"M\" ) (Pit)) (Penv))) (rule_return (Pbinop (AConcat) (Punop (ARec \"type\" )" +
			" (Pconst \"C2M\")) (Punop (ARec \"data\" ) (Pbinop (AConcat) (Punop (ARec \"client\" ) (Punop (ADot \"C\" )" +
			" (Penv))) (Punop (ARec \"marketer\" ) (Punop (ADot \"M\" ) (Penv)))))))))";
	private static final String test1Expanded =
			"(Punop (AFlatten) (PletIt (Pgetconstant \"WORLD\") (Pmap (PletEnv (PletEnv (Passert (Pbinop (AEq)" +
			" (Punop (ADot \"type\" ) (Pit)) (Pconst \"Client\"))) (PletEnv (Punop (ARec \"C\" ) (Pit)) (Penv)))" +
			" (Punop (AFlatten) (PletIt (Pgetconstant \"WORLD\") (Pmap (PletEnv (PletEnv (Passert (PletEnv" +
			" (Passert (Pbinop (AEq) (Punop (ADot \"type\" ) (Pit)) (Pconst \"Marketer\"))) (Pbinop (AContains)" + 
			" (Punop (ADot \"id\" ) (Punop (ADot \"data\" ) (Punop (ADot \"C\" ) (Penv)))) (Punop (ADot \"clients\" )" + 
			" (Punop (ADot \"data\" ) (Pit)))))) (PletEnv (Punop (ARec \"M\" ) (Pit)) (Penv))) (Punop (AColl)" +
			" (Pbinop (AConcat) (Punop (ARec \"type\" ) (Pconst \"C2M\")) (Punop (ARec \"data\" ) (Pbinop (AConcat)" +
			" (Punop (ARec \"client\" ) (Punop (ADot \"C\" ) (Penv))) (Punop (ARec \"marketer\" ) (Punop (ADot \"M\" )" +
			" (Penv)))))))))))))))";
	private static final String test2 = "(Punop (AFlatten) (PletIt (Pgetconstant \"WORLD\") (Pmap (PletEnv (PletIt" +
			" (PletIt (Punop (ACast \"entities.Customer\" ) (Pit)) (Pleft)) (PletEnv (Punop (ARec \"c\" ) (Pit)) (PletEnv" +
			" (Passert (Pbinop (AEq) (PletIt (Punop (AUnbrand) (Pit)) (PletIt (Punop (ADot \"age\" ) (Pit)) (Pit)))"+ 
			" (Pconst 32))) (PletIt (Penv) (Pit))))) (Punop (AColl) (Pbinop (ASConcat) (Punop (AToString)"+ 
			" (Pconst \"Customer =\")) (Punop (AToString) (PletIt (PletIt (Penv) (Punop (ADot \"c\" ) (Pit))) (PletIt"+ 
			" (Punop (AUnbrand) (Pit)) (PletIt (Punop (ADot \"name\" ) (Pit)) (Pit)))))))))))";
	
	/** Constructs the example in the ECOOP 2013 paper, Figure 6 */
	@Test
	public void Test1() {
		/* [when] it.type = “Client” */
		CampPattern itType = dot(CampPattern.IT, "type");
		CampPattern typeEqClient = eq(itType, new ConstPattern("Client"));
		/* ^ let env += [C : it] in env; */
		UnaryPattern Cit = rec("C", CampPattern.IT);
		CampPattern pand = pand(typeEqClient, new LetEnvPattern(Cit, CampPattern.ENV));
		/* when ... */
		WhenRule when1 = new WhenRule(pand); 
		/* [when] it.type = “Marketer” */
		CampPattern typeEqMarketer = eq(itType, new ConstPattern("Marketer"));
		/* ^ env.C.data.id containedIn it.data.clients */
		UnaryPattern envCdataId = dot(dot(dot(CampPattern.ENV, "C"), "data"), "id");
		UnaryPattern itDataClients = dot(dot(CampPattern.IT, "data"), "clients");
		BinaryPattern contained = new BinaryPattern(BinaryOperator.AContains, envCdataId,  itDataClients);
		pand = pand(typeEqMarketer, contained); 
		/* ^ let env += [M : it] in env; */
		UnaryPattern Mit = rec("M", CampPattern.IT);
		pand = pand(pand, new LetEnvPattern(Mit, CampPattern.ENV));
		/* when ... */
		WhenRule when2 = new WhenRule(pand);
		/* return [type : “C2M”]* 
            [data : [client : env.C]*
            [marketer : env.M]] */
		CampPattern type = rec("type", new ConstPattern("C2M"));
		CampPattern client = rec("client", dot(ConstPattern.ENV, "C"));
		CampPattern marketer = rec("marketer", dot(ConstPattern.ENV, "M"));
		CampPattern data = rec("data", concat(client, marketer));
		ReturnRule ret = new ReturnRule(concat(type, data));
		CampRule ans = when1.apply(when2.apply(ret));
		String result = ans.emit();
		System.out.println("Original (with rules):");
		System.out.println(result);
		Assert.assertEquals("incorrect raw result. ", test1Raw, result);
		CampPattern expanded = ans.convertToPattern();
		System.out.println("After expansion:");
		System.out.println(expanded.emit());
		Assert.assertEquals("incorrect expanded result. ", test1Expanded, expanded.emit());
		// Probably temporary (basis of new tests):
		System.out.println("After round trip through CALib");
		BridgeToML bridge = new BridgeToML();
		System.out.println(bridge.dumpCAMP(bridge.importCAMP(expanded)));
	}
	
	/** Constructs the equivalent of the test01 sample provided by qcert open source:
	  Example R01 :=
        punop AFlatten (pletIt ((pgetconstant "WORLD")) 
           (pmap (pletEnv 
              (pletIt 
                 (pletIt (punop (ACast ["entities.Customer"]) (pit)) (pleft))
                 (pletEnv (punop (ARec "c") (pit)) 
                   (pletEnv 
                     (passert (pbinop AEq 
                       (pletIt (punop AUnbrand (pit)) (pletIt (punop (ADot "age") (pit)) (pit))) (#` 32))) 
                     (pletIt (penv) (pit))
                   )
                 )
              ) 
              (punop AColl (pbinop ASConcat 
                (punop AToString (#` "Customer =")) 
                (punop AToString (pletIt (pletIt (penv) 
                  (punop (ADot "c") (pit))) (pletIt (punop AUnbrand (pit)) (pletIt (punop (ADot "name") (pit)) (pit)))))
              ))
           ))
        )
	 */
	@Test
	public void test2() throws Exception {
		CampPattern itop1 = new LetItPattern(new UnaryPattern(UnaryOperator.ACast, Collections.singletonList("entities.Customer"),
				CampPattern.IT), CampPattern.LEFT);
		CampPattern unbrandAge = new LetItPattern(unbrandIt(), 
				new LetItPattern(dot(CampPattern.IT, "age"), CampPattern.IT));
		CampPattern envAssert = new LetEnvPattern(new AssertPattern(eq(unbrandAge, new ConstPattern(new NatData(32)))), 
				new LetItPattern(CampPattern.ENV, CampPattern.IT));
		CampPattern itop2 = new LetEnvPattern(new UnaryPattern(UnaryOperator.ARec, "c", CampPattern.IT), envAssert);
		CampPattern envop1 = new LetItPattern(itop1, itop2);
		CampPattern cName = stringify(new LetItPattern(new LetItPattern(CampPattern.ENV, dot(CampPattern.IT, "c")), 
				new LetItPattern(unbrandIt(), new LetItPattern(dot(CampPattern.IT, "name"), CampPattern.IT))));
		CampPattern binop = new BinaryPattern(BinaryOperator.ASConcat, stringify(new ConstPattern(new StringData("Customer ="))), 
				cName);
		CampPattern envop2 = new UnaryPattern(UnaryOperator.AColl, binop);
		CampPattern map = new MapPattern(new LetEnvPattern(envop1, envop2));
		CampPattern ans = new UnaryPattern(UnaryOperator.AFlatten, new LetItPattern(new GetConstPattern("WORLD"), map));
		System.out.println("Original:");
		String result = ans.emit();
		System.out.println(result);
		Assert.assertEquals("incorrect result. ", test2, result);
		System.out.println("After round trip through CALib");
		BridgeToML bridge = new BridgeToML();
		System.out.println(bridge.dumpCAMP(bridge.importCAMP(ans)));
	}
}
