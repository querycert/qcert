/**
 * (c) Copyright IBM Corp. 2015-2017
 * Copyright (C) 2017 Joshua Auerbach 
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
package org.qcert.camp.translator;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.InputStream;
import java.io.Reader;
import java.util.Collections;
import java.util.EnumSet;
import java.util.Map;
import java.util.Map.Entry;

import org.qcert.util.SchemaUtil;
import org.qcert.util.SchemaUtil.ListType;
import org.qcert.util.SchemaUtil.ObjectType;
import org.qcert.util.SchemaUtil.PrimitiveType;
import org.qcert.util.SchemaUtil.Type;

import com.google.gson.JsonElement;
import com.ibm.rules.engine.compilation.CompilationPlugin;
import com.ibm.rules.engine.lang.semantics.SemClass;
import com.ibm.rules.engine.lang.semantics.SemModifier;
import com.ibm.rules.engine.lang.semantics.SemObjectModel;
import com.ibm.rules.engine.lang.semantics.SemType;
import com.ibm.rules.engine.lang.semantics.impl.SemObjectModelImpl;
import com.ibm.rules.engine.lang.semantics.mutable.SemMutableClass;
import com.ibm.rules.engine.lang.semantics.mutable.SemMutableObjectModel;
import com.ibm.rules.engine.outline.EngineOutline;
import com.ibm.rules.engine.rete.compilation.Constants.CompilationMode;
import com.ibm.rules.engine.rete.compilation.ReteCompiler;
import com.ibm.rules.engine.rete.compilation.ReteCompilerInput;
import com.ibm.rules.engine.ruledef.runtime.RuleEngine;
import com.ibm.rules.engine.ruledef.runtime.RuleEngineDefinition;
import com.ibm.rules.engine.ruledef.semantics.SemRule;
import com.ibm.rules.engine.ruledef.semantics.SemRuleLanguageFactory;
import com.ibm.rules.engine.ruledef.semantics.SemRuleLanguageFactoryImpl;
import com.ibm.rules.engine.ruledef.semantics.SemRuleset;
import com.ibm.rules.engine.ruledef.semantics.io.SemRuleSerializer;
import com.ibm.rules.engine.util.HName;

/**
 * Contains ODM specific mechanics for consuming ARL.
 * Can alternatively consume a serialized SemRule.
 * A heavily edited version of the original version, which did not have support for serialized SemRule but instead had support for
 *   parsing Berl, Defl, and Eqrl.
 */
public class ODMFrontEnd {
	/** Place to store the SemRule for retrieval */
	private SemRule rule;
	
	/** Place to store a SemRuleset associated with the rule, if any */
	private SemRuleset ruleset;

	/** Place to store the Engine.  Computed lazily when first requested but then saved.  */
	private RuleEngine engine;
	
	/** Place to store the object model for retrieval of it or the language factory */
	private SemMutableObjectModel model;

	/**
	 * Make a new ODMFrontEnd from an InputStream that supplies a SemRule in serialized form
	 * @param serialized the input stream
	 * @param schema the schema to use or null (if null, no types are added to the Object model initially and any types employed
	 *   must be native and loadable from the class path)
	 */
	public ODMFrontEnd(InputStream serialized, JsonElement schema) {
		model = createObjectModel(schema);
		SemRuleSerializer ser = new SemRuleSerializer();
		SemObjectModelImpl model = new SemObjectModelImpl(true);
		rule = ser.deSerializeRule(model, serialized);
	}
	
	/**
	 * Make a new ODMFrontEnd for a rule expressed in ARL and supplied by a Reader (not necessarily in a file)
	 * @param input the Reader that supplies the rule
	 * @param name the name of the rule to use in diagnostics during parsing; may be null if there is no meaningful name
	 * @param schema the schema to use or null (if null, no types are added to the Object model initially and any types employed
	 *   must be native and loadable from the class path)
	 * @throws Exception
	 */
	public ODMFrontEnd(Reader input, String name, JsonElement schema) throws Exception {
		SemMutableObjectModel model = createObjectModel(schema);
		ReteCompiler<ReteCompilerInput> reteCompiler = new ReteCompiler<>();
		if (!(input instanceof BufferedReader))
			input = new BufferedReader(input);
		if (name == null)
			name = "<unknown>";
		ruleset = reteCompiler.parse(input, name, Collections.<CompilationPlugin>emptyList(), model);
		if (ruleset.getRules().isEmpty()) throw new IllegalArgumentException("Arl parsing failed");
		rule = ruleset.getRules().get(0);
		this.model = (SemMutableObjectModel) ruleset.getObjectModel();
	}
	
	/**
	 * Make a new ODMFrontEnd for a rule expressed in ARL and contained in a file
	 * @param arlFile the name of the file containing the ARL rule
	 * @param schema the schema to use or null (if null, no types are added to the Object model initially and any types employed
	 *   must be native and loadable from the class path)
	 * @throws Exception
	 */
	public ODMFrontEnd(String arlFile, JsonElement schema) throws Exception {
		this(new FileReader(arlFile), arlFile, schema);
	}

	/**
	 * Provides the appropriate engine for all cases
	 * TODO we do not currently know how to supply the engine for the deserializing case
	 * @return the engine
	 * @throws Exception 
	 */
	public RuleEngine getEngine() throws Exception {
		if (engine == null) {
			if (ruleset == null)
				throw new UnsupportedOperationException("Dont know how to make an engine for the deserialized case");
			ReteCompilerInput compInput = new ReteCompilerInput(ruleset, null, null,
					CompilationMode.RVE_RETE);
			ReteCompiler<ReteCompilerInput> compiler = new ReteCompiler<ReteCompilerInput>();
			EngineOutline outline = compiler.compile(compInput);
			RuleEngineDefinition definition = (RuleEngineDefinition) outline
					.createEngineDefinition();
			engine = definition.createEngine();
		}
		return engine;
	}

	/**
	 * @return the factory
	 */
	public SemRuleLanguageFactory getFactory() {
		return new SemRuleLanguageFactoryImpl(model.getLanguageFactory());
	}
	
	/**
	 * @return the object model
	 */
	public SemObjectModel getObjectModel() {
		return model;
	}

	/**
	 * @return the rule
	 */
	public SemRule getRule() {
		return rule;
	}

	/**
	 * Make an object model, containing the information in a schema (which may be absent, causing the object model to contain only
	 *   standard builtin types)
	 * @param schema the schema in one of its various JSON encodings
	 * @return the model
	 */
	private SemMutableObjectModel createObjectModel(JsonElement schema) {
		SemMutableObjectModel model = new SemObjectModelImpl(true);
		if (schema != null)
			populateObjectModel(model, SchemaUtil.getSchema(schema));
		return model;
	}

	/**
	 * Make a SemClass, adding it to the model, and returning it 
	 * @param model the model
	 * @param type the ObjectType to be converted to a SemClass
	 * @return the converted SemClass
	 */
	private SemType makeClass(SemMutableObjectModel model, ObjectType type) {
		/* If the type is present as a native class, let that take precedence */
		SemClass maybe = model.loadNativeClass(type.brand);
		if (maybe != null)
			return maybe;
		/* Otherwise construct as best we can.  The following is good enough for ARL parsing and the like and qcert can take it from
		 *   there, but ODM will not be able to execute the result (for some reason).   */
		EnumSet<SemModifier> publik = EnumSet.of(SemModifier.PUBLIC);
		HName hname = model.getHNameFactory().getHName(type.brand);
		SemMutableClass cls = model.createClass(hname, publik);
		cls.addSuperclass(model.loadNativeClass(Object.class));
		for (Entry<String, SchemaUtil.Type> entry : type.attributes.entrySet()) {
			cls.createAttribute(entry.getKey(), publik, makeType(entry.getValue(), model));
		}
		return cls;
	}

	/** Make a SemType from the types that can appear in our schema format */
	private SemType makeType(Type type, SemMutableObjectModel model) {
		if (type instanceof PrimitiveType) {
			String tag = ((PrimitiveType) type).typeName;
			switch (tag) {
			case "Nat":
				return model.getType("int");
			case "Float":
				return model.getType("float");
			case "String":
				return model.loadNativeClass(String.class);
			default:
				throw new UnsupportedOperationException("Don't yet know how to handle encoded type " + tag);
			}
		}
		if (type instanceof ListType) {
			SemType element = makeType(((ListType) type).elementType, model);
			return model.loadNativeGenericClass("java.util.Collection", element);
		}
		return makeClass(model, (ObjectType) type);
	}

	/**
	 * Populate an object model from the "model" section of a schema
	 * @param model the model to populate
	 * @param map the "model" section of the relevant schema
s	 */
	private void populateObjectModel(SemMutableObjectModel model, Map<String, ObjectType> map) {
		for (ObjectType type : map.values()) {
			makeClass(model, type);
		}
	}
}
