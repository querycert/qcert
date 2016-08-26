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

import static org.qcert.camp.CampMacros.concat;
import static org.qcert.camp.CampMacros.dot;
import static org.qcert.camp.CampMacros.eq;
import static org.qcert.camp.CampMacros.pand;
import static org.qcert.camp.CampMacros.rec;

import org.junit.Assert;
import org.junit.Test;
import org.qcert.camp.pattern.BinaryOperator;
import org.qcert.camp.pattern.BinaryPattern;
import org.qcert.camp.pattern.CampPattern;
import org.qcert.camp.pattern.ConstPattern;
import org.qcert.camp.pattern.LetEnvPattern;
import org.qcert.camp.pattern.UnaryPattern;
import org.qcert.camp.rule.CampRule;
import org.qcert.camp.rule.ReturnRule;
import org.qcert.camp.rule.WhenRule;

/** Constructs the example in the ECOOP 2013 paper, Figure 6 */
public class Tests {
	private static final String compare = "(rule_when (pletEnv (passert (pbinop (AEq) (punop (ADot) (pit))" +
			" (pconst (dstring \"Client\")))) (pletEnv (punop (ARec) (pit)) (penv))) (rule_when (pletEnv (passert (pletEnv " +
			"(passert (pbinop (AEq) (punop (ADot) (pit)) (pconst (dstring \"Marketer\")))) (pbinop (AContains) (punop (ADot)" +
			" (punop (ADot) (punop (ADot) (penv)))) (punop (ADot) (punop (ADot) (pit)))))) (pletEnv (punop (ARec) (pit)) (penv))) " +
			"(rule_return (pbinop (AConcat) (punop (ARec) (pconst (dstring \"C2M\"))) (punop (ARec) (pbinop (AConcat) (punop " +
			"(ARec) (punop (ADot) (penv))) (punop (ARec) (punop (ADot) (penv)))))))))";

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
		String result = ans.emit(true);
		System.out.println(result);
		Assert.assertEquals("incorrect result. ", compare, result);
	}
}
