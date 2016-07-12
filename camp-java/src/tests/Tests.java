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
import org.qcert.camp.rule.CompleteRule;
import org.qcert.camp.rule.CompoundRule;
import org.qcert.camp.rule.ReturnRule;
import org.qcert.camp.rule.WhenRule;

/** Constructs the example in the ECOOP 2013 paper, Figure 6 */
public class Tests {
	private static final String compare = String.format(
    "rule_when (let ENV += assert AEq(ADot \"type\" (IT), \"Client\") in let ENV += ARec \"C\" (IT) in ENV) ;;%n" +
	"rule_when (let ENV += assert let ENV += assert AEq(ADot \"type\" (IT), \"Marketer\") in AContains(ADot \"id\" " + 
	   "(ADot \"data\" (ADot \"C\" (ENV))), ADot \"clients\" (ADot \"data\" (IT))) in let ENV += ARec \"M\" (IT) in ENV) ;;%n" +
	"rule_return (AConcat(ARec \"type\" (\"C2M\"), ARec \"data\" (AConcat(ARec \"client\" (ADot \"C\" (ENV)), " + 
	   "ARec \"marketer\" (ADot \"M\" (ENV))))))");

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
		CompleteRule ans = new CompleteRule(new CompoundRule(when1, when2), ret);
		String result = ans.emit();
		System.out.println(result);
		Assert.assertEquals("incorrect result. ", compare, result);
	}
}
