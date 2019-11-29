var entityMap = {
	"&" : "&amp;",
	"<" : "&lt;",
	">" : "&gt;",
	'"' : '&quot;',
	"'" : '&#39;',
	"/" : '&#x2F;'
};
function escapeHtml(string) {
	return String(string).replace(/[&<>"'\/]/g, function(s) {
		return entityMap[s];
	});
}
function getParameter(paramName, defaultValue) {
	elem = document.getElementById(paramName);
	if (elem != null) {
		return elem.value;
	} else {
		return defaultValue;
	}
}
function compileButton() {
	var input = {
		'source' : getParameter("source", ""),
		'target' : getParameter("target", ""),
		'exactpath' : getParameter("exactpath", "FillPath") === "ExactPath",
		'emitall' : getParameter("emitall", "EmitTarget") === "EmitAll",
		'eval' : false,
		'schema' : getParameter("schema", "{}"),
		'input' : getParameter("input", "{}"),
		'ascii' : getParameter("charset", "Greek") === "Ascii",
		'javaimports' : getParameter("java_imports", ""),
  	        'query' : document.getElementById("query").value,
     	        'optims' : getParameter("optim","[]")
	};
	document.getElementById("result").innerHTML = "[ Query is compiling ]";
	var handler = function(compilationResult) {
		compiledQuery = compilationResult.result;
		document.getElementById("result").innerHTML = escapeHtml(compiledQuery);
		displayAllResults(compilationResult.emitall);
	}
	qcertWhiskDispatch(input, handler);
}
function verify(result, expected) {
	result = result[0]; // TODO is this always right?  
	if (result.length != expected.length)
		return false;
	for (var i = 0; i < result.length; i++) {
		var resultMember = result[i];
		var expectedMember = expected[i];
		if (resultMember.constructor == Array
				&& expectedMember.constructor == Array) {
			if (!verify(resultMember, expectedMember))
				return false;
		} else if (resultMember != expectedMember)
			return false;
	}
	return true;
}
function compileForEval() {
	var input = {
		'source' : document.getElementById("source").value,
		'target' : document.getElementById("target").value,
		'exactpath' : document.getElementById("exactpath").value === "ExactPath",
		'emitall' : document.getElementById("emitall").value === "EmitAll",
		'eval' : true,
		'schema' : document.getElementById("schema").value,
		'input' : document.getElementById("input").value,
		'ascii' : document.getElementById("charset").value === "Ascii",
		'javaimports' : document.getElementById("java_imports").value,
		'query' : document.getElementById("query").value,
	        'optims' : [],
	};
	console.log(input);
	var handler = function(compilationResult) {
		evalQuery = compilationResult.eval;
		document.getElementById("execresult").innerHTML = escapeHtml(evalQuery);
	}
	qcertWhiskDispatch(input, handler);
}
function performJsEvaluation() {
	// Processing is delegated to a web-worker
	try {
		var inputString = document.getElementById("input").value;
		var schemaText = document.getElementById("schema").value;
		// Worker is at global scope, making it accessible to the kill button
		worker = new Worker("evalWorker.js");
		worker.onmessage = function(e) {
			document.getElementById("execresult").innerHTML = escapeHtml(e.data);
		}
		worker.onerror = function(e) {
			document.getElementById("execresult").innerHTML = escapeHtml(e.message);
		}
		worker.postMessage([inputString, schemaText, compiledQuery]);
	} catch (err) {
		document.getElementById("execresult").innerHTML = escapeHtml(err.message);
	}
}
function killButton() {
	worker.terminate();
	document.getElementById("execresult").innerHTML = "[ Execution terminated ]";
}
function executeButton() {
	var target = document.getElementById("target").value;
	document.getElementById("execresult").innerHTML = "[ Evaluating ]";
	if (target != "js")
		compileForEval()
	else {
		performJsEvaluation();
	}
}
function clearButton() {
	document.getElementById("result").innerHTML = "";
	document.getElementById("execresult").innerHTML = "";
	document.getElementById("allresults").innerHTML = "";
}
function addOption(sel, lang) {
	var opt = document.createElement("option");
	opt.setAttribute("value", lang);
	var t = document.createTextNode(lang);
	opt.appendChild(t);
	sel.appendChild(opt);
}
function displayAllResults(allresults) {
	document.getElementById("allresults").innerHTML = "";
	for (var i = 0; i < allresults.length; i++) {
		addResult(allresults[i].file, allresults[i].lang, allresults[i].value);
	}
}
function addResult(file, lang, value) {
	var allres = document.getElementById("allresults");
	var l = document.createElement("b");
	var t1 = document.createTextNode(lang);
	l.appendChild(t1);
	var query = document.createElement("pre");
	var t2 = document.createTextNode(value);
	query.appendChild(t2);
	allres.appendChild(l);
	allres.appendChild(query);
}
function addPath() {
	var li = document.createElement("LI");
	var sel = document.createElement("SELECT");
	li.appendChild(sel);
	addOption(sel, "camp_rule");
	addOption(sel, "camp");
	addOption(sel, "oql");
	addOption(sel, "lambda_nra");
	addOption(sel, "nra");
	addOption(sel, "nraenv");
	addOption(sel, "nnrc");
	addOption(sel, "nnrcmr");
	addOption(sel, "cldmr");
	addOption(sel, "dnnrc");
	addOption(sel, "dnnrc_typed");
	addOption(sel, "js");
	addOption(sel, "java");
	addOption(sel, "spark_rdd");
	addOption(sel, "spark_df");
	addOption(sel, "cloudant");
	document.getElementById("path").appendChild(li);
	return false;
}
function handleFile(files, output) {
	console.log("File handler called");
	if (files.length > 0) {
		var reader = new FileReader();
		var file = files[0];
		document.getElementById(output).innerHTML = "[ Reading ]";
		if (file.name.endsWith(".sem")) {
			reader.onload = function(event) {
				var contents = btoa(String.fromCharCode.apply(null,
						new Uint8Array(event.target.result)))
				document.getElementById(output).innerHTML = contents;
			}
			reader.readAsArrayBuffer(file);
		} else {
			reader.onload = function(event) {
				var contents = escapeHtml(event.target.result);
				if (output == "schema" && isSQLSchema(contents))
					convertSQLSchema(contents);
				else
					document.getElementById(output).innerHTML = contents;
			}
			reader.readAsText(file);
		}
	}
}
// Determine if a String contains a SQL schema.  Not intended to be foolproof but just to discriminate the two supported schema
// notations (SQL and JSON) when the input is at least mostly valid.
function isSQLSchema(schemaText) {
	/* A SQL schema should have the word "create" in it but SQL is case insensitive  */
	var create = schemaText.search(/create/i);
	if (create < 0)
		return false;
	var brace = schemaText.indexOf('{');
	if (brace >= 0 && brace < create)
		/* Word create is coincidentally appearing inside what is probably a JSON schema */
		return false;
	/* Looking more like SQL.  Drop any blanks that follow 'create' */
	var balance = schemaText.substring(create + 6).trim();
	/* The next word must be 'table' (case insensitive) */
	var table = balance.search(/table/i);
	return table == 0;
}
function convertSQLSchema(toConvert) {
	var process = function(result) {
		document.getElementById("schema").innerHTML = result;
	}
	var result = preProcess(toConvert, "sqlSchema2JSON", process);
}
function handleCSVs(files) {
	console.log("CSV file handler called");
	var readFiles = {};
	function readFile(index) {
		if (index >= files.length) {
			completeCSVs(readFiles);
			return;
		}
		var file = files[index];
		var reader = new FileReader();  
		reader.onload = function(event) {
			var typeName = file.name.endsWith(".csv") ? file.name.substring(0, file.name.length - 4) : file.name;
			readFiles[typeName] = event.target.result;
			readFile(index+1);
		}
		reader.readAsText(file);
	}
	readFile(0);
}
function completeCSVs(readFiles) {
	var delimiter = document.getElementById("delimiter").value; 
	var schema = JSON.parse(document.getElementById("schema").value);
	var toSend = JSON.stringify({schema: schema, delimiter: delimiter, data: readFiles});
	var process = function(result) {
		document.getElementById("input").innerHTML = result;
	}
	var result = preProcess(toSend, "csv2JSON", process);
}
