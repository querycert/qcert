/*
 * (c) Copyright IBM Corp. 2015 All Rights Reserved
 */
package testing.runners;

import java.util.List;

import java.io.FileReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.PrintWriter;
import java.io.StringWriter;

import java.util.Map;
import java.util.Map.Entry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Iterator;

import java.lang.reflect.Type;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import org.apache.commons.collections.Bag;
import org.apache.commons.collections.bag.HashBag;

import com.cloudant.client.api.CloudantClient;
import com.cloudant.client.api.Database;
import com.cloudant.client.api.View;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.reflect.TypeToken;

import org.junit.Assert;

public class RunCloudant {
	/** The name that the result value will have after Javascript evaluation by a script engine */
	public static final String RESULT_VALUE = "resultValue";
	
	/** Number of seconds to wait after submission to cloudant (and also on each retry) */
        public static final int CLOUDANT_QUERY_DELAY = 20;

	/** Number of seconds to wait during document loading into cloudant (to fit within rate limitations constraints on free trial) */
        public static final int CLOUDANT_RATE_DELAY = 1;

	/** Number of retries to attempt with Cloudant before declaring failure */
        public static final int CLOUDANT_RETRY_LIMIT = 20;

        private static List<String> jsonArrayToList(JsonArray param) {
	    Type type = new TypeToken<List<String>>(){}.getType();
	    List<String> list = new Gson().fromJson(param, type);
	    System.out.println("Cloudant Last expression inputs:" + list.toString());
	    
	    return list;
        }

	/**
	 * Parse the I/O file, producing a JsonObject with three members (input, output, inheritance)
	 * @param ioFile the path name of the I/O file
	 * @return a JsonObject resulting from the parsing
	 */
	public static JsonObject parseJsonFileToObject(String ioFile) throws Exception {
		return new JsonParser().parse(new FileReader(ioFile)).getAsJsonObject();
	}

	/**
	 * Flatten any embedded Json arrays into a one-level array
	 * @param toFlatten the JsonArray to flatten
	 * @param into the JsonArray we are flattening into
	 * @return the into argument for convenience
	 */
	private static JsonArray flatten(JsonArray toFlatten, JsonArray into) {
		for (JsonElement e : toFlatten.getAsJsonArray()) {
			if (e.isJsonArray()) 
				flatten((JsonArray) e, into);
			else
				into.add(e);
		}
		return into;
	}

	/**
	 * Given a JsonObject, return another that has the same "real" information but is canonical in terms of
	 * <ol><li>whether the type is called "type" (legacy CAMP project format) or "$class" (ODM format) and
	 * <li>whether the non-type portion of the object is enclosed in a "data" object (legacy CAMP project
	 *        format) or at the same level (ODM format)</ol>
	 * @param object the JsonObject
	 * @return the canonical form
	 */
	private static JsonObject canonicalize(JsonObject object) {
		JsonElement cls = object.get("$class");
		if (cls != null) {
			JsonObject data = new JsonObject();
			for (Entry<String, JsonElement> entry : object.entrySet()) {
				String name = entry.getKey();
				if (name.charAt(0) == '$') continue;
				data.add(name, entry.getValue());
			}
			JsonObject replacement = new JsonObject();
			JsonArray brands = new JsonArray();
			brands.add(cls);
			replacement.add("type", brands);
			replacement.add("data", data);
			return replacement;
		}
		return object;
	}

	/**
	 * Convert a JsonElement into something (Bag, Map, or self) that will give an accurate answer to the
	 *   equals() method, ignoring order
	 * @param element the element to convert
	 * @return the converted element
	 */
	private static Object makeComparable(JsonElement element) {
		if (element instanceof JsonObject) {
			JsonObject obj = canonicalize((JsonObject) element);
			Map<String,Object> result = new HashMap<>();
			for (Entry<String,JsonElement> entry : obj.entrySet()) {
				result.put(entry.getKey(), makeComparable(entry.getValue()));
			}
			return result;
		}
		if (element instanceof JsonArray) {
			JsonArray array = flatten((JsonArray) element, new JsonArray());
			Bag result = new HashBag();
			for (JsonElement e : array) {
				result.add(makeComparable(e));
			}
			return result;
		}
		// JsonNull and JsonPrimitive already have reasonable equality methods
		return element;
	}

	/**
	 * Compare two JsonArray objects for logical equality as part of validating a test
	 * @param expected the expected result
	 * @param actual the actual result
	 * @return true on successful comparison, false on failure
	 */
	private static boolean compareForValidity(JsonArray expected,
			JsonArray actual) {
		/* Compare the two */
		Object actualCompare = makeComparable(actual);
		Object expectedCompare = makeComparable(expected);
		if (actualCompare.equals(expectedCompare)) {
		    System.out.println("Success!  Expected and actual: " + actual);
		    return true;
		}
		System.out.println("Expected: " + expectedCompare);
		System.out.println("Actual: " + actualCompare);
                return false;
	}
    
	/**
	 * Validate the result of a Cloudant query against the expected output from the JSON I/O file
	 * @param result the cloudant query result as a JsonArray (requiring some pre-processing)
	 * @param compare the expected results, also as a JsonArray
	 */
	private static boolean validateCloudantOutput(JsonArray result, JsonArray compare) throws Exception {
		JsonArray realResult = new JsonArray();
		Iterator<JsonElement> iterator = result.iterator();
		while (iterator.hasNext()) {
			JsonObject elem = iterator.next().getAsJsonObject();
			realResult.add(elem.get("value"));
		}
		return compareForValidity(compare, realResult);
	}

	/**
	 * Utility for running a test through cloudant
	 * @param designDoc the File for the generated design document (JSON)
	 * @param postExpr the JS last expression to compute the final result
	 * @param postInputs the input databases for the JS last expression 
	 * @param inputJson the input to test with as JSON
	 * @param outputJson the expected results as JSON
	 */
         private static void runCloudantLast(CloudantClient client, JsonArray designList, String postExpr, JsonArray postInputs, JsonArray inputJson, JsonArray outputJson) throws Exception {
		/* Declare resources to be cleaned up on failure */
		List<String> allDBs = new ArrayList<>();
		String lastDBCopy = null;
		String lastParams = null;
		List<String> postInputList = jsonArrayToList(postInputs);
		Map<String,CloudantOut> dbParams = new LinkedHashMap<String,CloudantOut>();

		try {
			/* Create all the databases (possibly removing stray copies from earlier) and load their
			 * design documents.  Remember the first Database because it will get the data, and delay
			 * loading its design document until after the data (for greater realism).
			 */
			Database mainDB = null;
			JsonObject mainDesign = null;
			String solution = null;
			List<String> existingDbs = client.getAllDbs();
			String viewName = null;
			for (JsonElement e : designList) {
				JsonObject quad = e.getAsJsonObject();
				String dbName = quad.get("dbname").getAsString();
				CloudantOut cloudantOut = null; // Variable that will be populated with reverse mapping from dbcopy to dbname+default
				if (existingDbs.contains(dbName)) {
				    System.out.println("Deleting old copy of database " + dbName);
				    client.deleteDB(dbName);
				}
				System.out.println("Creating database " + dbName);

				Database db = client.database(dbName, true);
				JsonObject design = quad.get("design").getAsJsonObject();
				JsonObject views = design.getAsJsonObject("views");
				viewName = views.entrySet().iterator().next().getKey();
				JsonObject view = views.get(viewName).getAsJsonObject();
				// if dbName is in the list of inputs for last expression add it to dbParams with the corresponding default expression
				for (String str: postInputList) {
				    String dbCopyName = view.get("dbcopy").getAsString();
				    System.out.println("Found dbCopy: " + dbCopyName);
				    String dbDefault = optDefault(view); // Get the default expression for that database
				    System.out.println("Checking dbcopy: " + dbCopyName + " against input " + str);
				    if (str.equals(dbCopyName)) {
					cloudantOut = new CloudantOut(dbName,viewName,dbDefault,dbCopyName);
					dbParams.put(dbCopyName,cloudantOut);
				    }
				}
				String dbCopy = view.get("dbcopy").getAsString();
				design.add("_id", new JsonPrimitive("_design/"+dbName));
				if (mainDB == null) {
					/* Special handling for the main db */
					solution = dbName;
					mainDB = db;
					mainDesign = design;
				} else {
					/* Other designs can be loaded early */
				    System.out.println("Loading design document into " + dbName);
				    String err = db.save(design).getError();
				    if (err != null)
					System.err.println(err);
				}

				lastDBCopy = dbCopy;
				allDBs.add(dbName);
			}

			/* Hydrate the input JSON String as a JSON object and load it into the first database */
			System.out.printf("Pausing for %d second (rate limitation)%n",CLOUDANT_RATE_DELAY);
			Thread.sleep(CLOUDANT_RATE_DELAY * 1000);
			System.out.println("Loading inputs into database");
			int rate = 0;
			for (JsonElement e : inputJson) {
			    // Rate limiter
			    Object toStore = e.getAsJsonObject();
			    String err = mainDB.save(toStore).getError();
			    rate++;
			    if (err != null) {
				System.err.println(err);
			    }
			    // If reaching 10, wait a second
			    if (rate >= 10) {
				System.out.printf("Pausing for %d second (rate limitation)%n",CLOUDANT_RATE_DELAY);
				Thread.sleep(CLOUDANT_RATE_DELAY * 1000);
				Thread.sleep(1000);
			    }
			}
			
			/* Add the design document to the first database to activate the chain */
			System.out.println("Loading main design document into " + solution);
			String err = mainDB.save(mainDesign).getError();
			if (err != null)
				System.err.println(err);
			
			/* Retrieve result */
			System.out.printf("Obtaining result from cloudant%n");
			for (int i = 0; i < CLOUDANT_RETRY_LIMIT; i++) {
			    System.out.format("Pausing for %d seconds%n", CLOUDANT_QUERY_DELAY);
			    Thread.sleep(CLOUDANT_QUERY_DELAY * 1000);
			    System.out.format("Trying view retrieval (%d of %d)%n", i+1, CLOUDANT_RETRY_LIMIT);
			    String result = getCloudantResult(client, dbParams, postExpr);
			    validateOutput(result, outputJson);
			    return;
			}
			Assert.fail("No valid result after exhausting retries");
		} finally {
			if (client != null) {
			    for (String db : allDBs) {
				System.out.println("Deleting database " + db);
				client.deleteDB(db);
			    }
			    if (lastDBCopy != null) {
				System.out.println("Deleting database " + lastDBCopy);
				try {
				    client.deleteDB(lastDBCopy);
				} catch (org.lightcouch.NoDocumentException e) {
				    System.out.println("Database " + lastDBCopy + " cannot be deleted: does not exists");
				}
			    }
			    System.out.println("Shutting down client");
			    client.shutdown();
			}
		}
	}
	
	/**
	 * Validate the output from a js, java, spark_rdd, or spark_dataset
	 * @param result the actual result
	 * @param expected the expected result
	 */
	private static void validateOutput(String result, JsonArray expected) {
		JsonParser parser = new JsonParser();
		if (!compareForValidity(expected, parser.parse(result).getAsJsonArray()))
			Assert.fail("Results were incorrect");
	}
    
	/**
	 * Accesses the (optionally present) dbdefault field in the JSON artifact for Cloudant
	 * @param view the Json Object containing the current view
	 */
        public static String optDefault(JsonObject view) {
	    JsonElement odef = view.get("dbdefault");
	    if (odef != null) return odef.getAsString();
	    else return null;
        }
    
        private static JsonArray getCloudantDB(CloudantClient client, String sourceDbName, String viewName, String dbDefaultExpr) throws Exception {
	    // Access the view
	    Database db = client.database(sourceDbName, true);
	    Reader rdr = null;
	    View view = db.view(sourceDbName + "/" + viewName);
	    InputStream query;
	    try {
		try { 
		    query = view.queryForStream();
		} catch (Throwable t) {
		    System.err.println("Cloudant query error:");
		    t.printStackTrace();
		    if (t instanceof RuntimeException) throw (RuntimeException) t;
		    if (t instanceof Error) throw (Error) t;
		    throw new IllegalStateException();
		}
		rdr = new InputStreamReader(query, "UTF-8");
		JsonArray result = new JsonParser().parse(rdr).getAsJsonObject().getAsJsonArray("rows");
		rdr.close();
		JsonArray realResult = new JsonArray();
		Iterator<JsonElement> iterator = result.iterator();
		// For empty database, fall back to defaultExpr
		if (!(iterator.hasNext())) {
		    if (dbDefaultExpr != null) return callJSDefaultFun(dbDefaultExpr);
		    else return new JsonArray();
		}
		while (iterator.hasNext()) {
			JsonObject elem = iterator.next().getAsJsonObject();
			realResult.add(elem.get("value"));
		}
		return realResult;
	    } finally {
		if (rdr != null) {
		    System.out.println("Closing query reader");
		    rdr.close();
		}
	    }
	}
    
	/**
	 * Call a JS function with JSON parameters (Gson)
	 * @param funName the name of the function being called
	 * @param jsClosure the function definition as a String
	 * @param jsParams a list of JSON values as Strings
	 */
    	public static JsonArray callJSDefaultFun(String jsClosure) throws ScriptException {
	    String funRes = callJSFun("db_default", jsClosure, new ArrayList<JsonArray>());
	    return (new JsonParser().parse("["+funRes+"]").getAsJsonArray());
	}

	/**
	 * Utility to get the result of a Cloudant entity query
	 * @param client the Cloudant Client
	 * @param dbParams the set of pairs of dbnames/default JS expressions, where the default is used to compute the result when the database is empty
	 * @param dbLast the last JS expression, computes the final result from the set of database results
	 */
         private static String getCloudantResult(CloudantClient client, Map<String,CloudantOut> dbParams, String lastExpr) throws Exception {
	     System.out.println("Getting Cloudant result for dbParams:" + dbParams.toString());
	     ArrayList<JsonArray> dbResults = new ArrayList<JsonArray>();

	     for (Entry<String, CloudantOut> entry : dbParams.entrySet()) {
		 String dbName = entry.getKey();
		 CloudantOut cloudantOut = entry.getValue();
		 dbResults.add(getCloudantDB(client,cloudantOut.getDbName(), cloudantOut.getViewName(),cloudantOut.getDefaultExpr()));
	     }
	     // Execute last expression
	     String result = callJSFun("db_post", lastExpr, dbResults);
	     return result;
	}
    
	/**
	 * Construct the parameters for a JS function call
	 * @param jsParams a list of keys
	 */
        public static String aggParams(ArrayList<JsonArray> jsParams) {
	    StringWriter swtr = new StringWriter();
	    PrintWriter wtr = new PrintWriter(swtr);
	    Iterator<JsonArray> iterator = jsParams.iterator();
	    if (iterator.hasNext()) {
		wtr.printf(iterator.next().toString());
		while (iterator.hasNext()) {
		    wtr.printf(",");
		    wtr.printf(iterator.next().toString());
		}
		System.out.println(swtr.toString());
		return swtr.toString();
	    }
	    else return "";
	}

	/**
	 * Call a JS function with JSON parameters (Gson)
	 * @param funName the name of the function being called
	 * @param jsClosure the function definition as a String
	 * @param jsParams a list of JSON values as Strings
	 */
    	public static String callJSFun(String funName, String jsClosure, ArrayList<JsonArray> jsParams) throws ScriptException {
    		ScriptEngineManager factory = new ScriptEngineManager();
    		ScriptEngine engine = factory.getEngineByName("JavaScript");
    		engine.eval(jsClosure); // Add the closure
    		String funCall = RESULT_VALUE + " = JSON.stringify(" + funName + "(" + aggParams(jsParams) + "));"; // Create the function call
    		engine.eval(funCall);
		String result = (String) engine.get(RESULT_VALUE);
		//System.out.println(result);
		return result;
	}

        public static void main(String[] args)  throws Exception {
	    /* Input to the runner */
	    String inputFile = null;
	    String designFile = null;

	    String cloudantUser = System.getProperty("cloudant_user");
	    String cloudantPasswd = System.getProperty("cloudant_password");
	    CloudantClient client = new CloudantClient(cloudantUser, cloudantUser, cloudantPasswd);
	    System.out.println("Connected to Cloudant");
	    System.out.println("Server Version: " + client.serverVersion());

	    /* Useful for testing the credentials: */
	    //List<String> databases = client.getAllDbs();
	    //System.out.println("All my databases : ");
	    //for ( String db : databases ) {
	    //	System.out.println(db);
	    //}

	    JsonObject ioParts = null;
    
	    for (int i = 0; i < args.length; i++) {
		String arg = args[i];
		// Must have a -input option for the input JSON
		if ("-input".equals(arg)) {
		    inputFile = args[i+1]; i++;
		    ioParts = parseJsonFileToObject(inputFile);
		} else {
		    JsonObject designs_and_post = parseJsonFileToObject(arg);
		    /* Run the test */
		    runCloudantLast(client,
				    designs_and_post.get("designs").getAsJsonArray(),
				    designs_and_post.get("post").getAsString(),
				    designs_and_post.get("post_input").getAsJsonArray(),
				    ioParts.get("input").getAsJsonObject().get("WORLD").getAsJsonArray(),
				    ioParts.get("output").getAsJsonArray());
		}
	    }
	}
}
