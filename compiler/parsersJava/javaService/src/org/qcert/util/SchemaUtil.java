/**
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
package org.qcert.util;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Contains utilities to convert JSON-formatted schemas into a more convenient form.  We use a simple inheritance of type representations.
 * <p>A <b>Type</b> is one of the following (the general case represented by a marker interface)
 * <ul><li>a <b>PrimitiveType</b> (containing a string type name), 
 * <li>a <b>ListType</b> (containing an element Type),
 * <li>an <b>ObjectType</b>, which has a brand and a attributes.  The attributes are represented as an ordered map from names 
 *   to <b>Type</b> objects.
 * <li>A schema is just a map from brands to <b>ObjectTypes</b> with those brands.  
 *   
 */
public class SchemaUtil {
	private SchemaUtil() {}
	
	/**
	 * Utility to derive the convenient schema form from various JSON encodings.  We support several formats.
	 * <ul><li>The so-called "I/O" file format, in which there is a "schema" member.
	 * <li>A JSON object consisting only of the schema (the same as the "schema" member of the I/O file but as a simple JSON object in a file
	 *   by itself)
	 * <li>A JSON object consisting only of the model portion of the schema.
	 * <li>A simplified form of the model portion of the schema in which the brandTypes and typeDefs are collapsed into a single
	 *   array of JSON objects, with each object having a "brand" and "typeDef" member (unifying on the "type name" which is not really
	 *   needed here)
	 * </ul>
	 * @param encoded a JsonElement encoding a schema in one of the supported formats
	 * @return a Map from brands to ObjectTypes defining the attributes associated with those brands
	 */
	public static Map<String, ObjectType> getSchema(JsonElement encoded) {
		if (encoded.isJsonObject()) {
			JsonObject objForm = encoded.getAsJsonObject();
			/* Deal with possibly different levels of wrapping */
			if (objForm.has("schema"))
				objForm = objForm.get("schema").getAsJsonObject();
			if (objForm.has("model")) // now obsolete but may persist in some corners
				objForm = objForm.get("model").getAsJsonObject();
			if (objForm.has("brandTypes") && objForm.has("typeDefs")) {
				JsonArray brandTypes = objForm.get("brandTypes").getAsJsonArray();
				JsonArray typeDefs = objForm.get("typeDefs").getAsJsonArray();
				return getSchemaFromBrandsAndTypedefs(brandTypes, typeDefs);
			} else if (objForm.has("types"))
				return getSchemaFromTypes(objForm.get("types").getAsJsonArray());
			else
				throw new IllegalArgumentException("Uninterpretable JSON element");
		} else if (encoded.isJsonArray())
			return getSchema(encoded.getAsJsonArray());
		else
			throw new IllegalArgumentException("Uninterpretable JSON element");
	}
	
	public static Map<String, ObjectType> getGlobalsFromSchema(JsonObject schema) {
		/* Deal with possibly different levels of wrapping */
		if (schema.has("schema"))
			schema = schema.get("schema").getAsJsonObject();
		if (schema.has("model")) // now obsolete but may persist in some corners
			schema = schema.get("model").getAsJsonObject();
		Map<String, ObjectType> ans = new HashMap<>();
		if (schema.has("globals")) {
			schema = schema.get("globals").getAsJsonObject();
			if (schema.size() == 1 && schema.has("WORLD"))
				// We heuristically assume the globals are uninteresting in the "one WORLD" case.  Use getSchema if the important
				// information is contained in the branded types.
				return ans;
			for (Entry<String, JsonElement> member : schema.entrySet()) {
				String typeName = member.getKey();
				JsonObject typeDef = member.getValue().getAsJsonObject().get("type").getAsJsonObject().get("$coll").getAsJsonObject();
				ans.put(typeName, makeObjectType(typeName, typeDef));
			}
		}
		return ans;
	}

	/**
	 * Utility to derive a convenient schema from two arrays, one pairing brands with type names, and the other pairing type names
	 *   with typedefs.  This is one form in which schemas are encoded (e.g. in the I/O file)
	 * @param brandTypes the array of pairs linking brands to type names
	 * @param typeDefs the array of pairs linking type names to type defs
	 * @return the convenient form of the schema
	 */
	public static Map<String, ObjectType> getSchemaFromBrandsAndTypedefs(JsonArray brandTypes, JsonArray typeDefs) {
		Map<String, String> brandMap = new HashMap<>();
		for (JsonElement pair : brandTypes) {
			JsonObject brandPair = pair.getAsJsonObject();
			brandMap.put(brandPair.get("typeName").getAsString(), brandPair.get("brand").getAsString());
		}
		Map<String, ObjectType> result = new HashMap<>();
		for (JsonElement pair : typeDefs) {
			JsonObject typePair = pair.getAsJsonObject();
			String brand = brandMap.get(typePair.get("typeName").getAsString());
			result.put(brand, makeObjectType(brand, typePair.get("typeDef").getAsJsonObject()));
		}
		return result;
	}

	/**
	 * Utility to derive a convenient schema from a single array which pairs brand names with typedefs.  Unlike getSchemaFromBrandsAndTypedefs, this encoding can't handle
	 *   embedded objects (other than collections).  Also, it is not currently the standard for I/O files.  However it is more straightforward to produce in many cases.
	 * @param types the JsonArray of types as brand/typeDef pairs
	 * @return the simplified schema
	 */
	public static Map<String, ObjectType> getSchemaFromTypes(JsonArray types) {
		Map<String, ObjectType> result = new HashMap<>();
		for (JsonElement pair : types) {
			JsonObject typePair = pair.getAsJsonObject();
			String brand = typePair.get("brand").getAsString();
			result.put(brand, makeObjectType(brand, typePair.get("typeDef").getAsJsonObject()));
		}
		return result;
	}

	/**
	 * Make an ObjectType from a brand name and typeDef
	 * @param brand the brand name
	 * @param typeDef the typeDef (as a JsonObject)
	 * @return the ObjectType
	 */
	private static ObjectType makeObjectType(String brand, JsonObject typeDef) {
		ObjectType ans = new ObjectType(brand);
		for (Entry<String, JsonElement> attr : typeDef.entrySet()) {
			ans.addAttribute(attr.getKey(), makeType(attr.getValue()));
		}
		return ans;
	}

	/**
	 * Make a Type from a JsonElement representing a Type.  
	 * TODO support for embedded objects (other than collections) is incomplete.
	 * @param type the JsonElement to be made into a Type
	 * @param brandMap the map from type names to brands in the event of an embedded objectl
	 * @return the Type
	 */
	private static Type makeType(JsonElement type) {
		if (type.isJsonPrimitive() && type.getAsJsonPrimitive().isString()) {
			return new PrimitiveType(type.getAsJsonPrimitive().getAsString());
		}
		// Other than primitive types and object type references we only support the $coll convention at this time
		JsonElement coll = type.getAsJsonObject().get("$coll");
		if (coll == null)
			throw new UnsupportedOperationException("Don't yet know how to handle encoded type " + type);
		Type element = makeType(coll);
		return new ListType(element);
	}
	
	/** List Type */
	public static class ListType implements Type {
		public final Type elementType;
		public ListType(Type elementType) {
			this.elementType = elementType;
		}
	}

	/** Object Type */
	public static class ObjectType implements Type {
		public final String brand;
		public final LinkedHashMap<String, Type> attributes = new LinkedHashMap<>();
		public ObjectType(String brand) {
			this.brand = brand;
		}
		public void addAttribute(String name, Type type) {
			attributes.put(name, type);
		}
	}
	
	/** Primitive Type */
	public static class PrimitiveType implements Type {
		public final String typeName;
		public PrimitiveType(String typeName) {
			this.typeName = typeName;
		}
	}
	
	/** Marker interface for all types */
	public interface Type {}
}
