var entityMap = {
		"&": "&amp;",
		"<": "&lt;",
		">": "&gt;",
		'"': '&quot;',
		"'": '&#39;',
		"/": '&#x2F;'
};
function escapeHtml(string) {
	return String(string).replace(/[&<>"'\/]/g, function (s) {
		return entityMap[s];
	});
}
	  function getParameter(paramName,defaultValue) {
	      elem = document.getElementById(paramName);
	      if (elem != null) {
		  return elem.value;
	      } else {
		  return defaultValue;
	      }
	  }
      function compileButton() {
	  var input = { 'source' : getParameter("source",""),
			'target' : getParameter("target",""),
			'exactpath' : getParameter("exactpath","FillPath") === "ExactPath",
			'emitall' : getParameter("emitall","EmitTarget") === "EmitAll",
			'eval' : false,
			'schema' : getParameter("schema","{}"),
			'input' : getParameter("input","{}"),
			'ascii' : getParameter("charset","Greek") === "Ascii",
			'javaimports' : getParameter("java_imports",""),
			'query' : document.getElementById("query").value
		      };
	  var schema = getParameter("schema","{}");
	  compilationResult = qcertPreCompile(input, schema);	
	  compiledQuery = compilationResult.result;
	  document.getElementById("result").innerHTML = escapeHtml(compiledQuery);
	  displayAllResults(compilationResult.emitall);
      }
function verify(result, expected) {
	if (result.length != expected.length)
		return false;
	for (var i = 0; i < result.length; i++) {
		var resultMember = result[i];
		var expectedMember = expected[i];
		if (resultMember.constructor == Array && expectedMember.constructor == Array) {
			if (!verify(resultMember, expectedMember))
				return false;
		} else if (resultMember != expectedMember)
			return false;
	}
	return true;
}
function compileForEval() {
	var input = { 'source' : document.getElementById("source").value,
			'target' : document.getElementById("target").value,
			'exactpath' : document.getElementById("exactpath").value === "ExactPath",
			'emitall' : document.getElementById("emitall").value === "EmitAll",
			'eval' : true,
			'schema' : document.getElementById("schema").value,
			'input' : document.getElementById("input").value,
			'ascii' : document.getElementById("charset").value === "Ascii",
			'javaimports' : document.getElementById("java_imports").value,
			'query' : document.getElementById("query").value,
	};
	var schema = document.getElementById("schema").value;
	compilationResult = qcertPreCompile(input, schema);	
	evalQuery = compilationResult.eval;
	document.getElementById("execresult").innerHTML = escapeHtml(evalQuery);
}
function performJsEvaluation() {
	var io = JSON.parse(document.getElementById("input").value);
	var input = ("input" in io) ? io.input : io;
	var schemaText = document.getElementById("schema").value;
	var schema = JSON.parse(schemaText);
	inheritance = ("hierarchy" in schema) ? schema.hierarchy : ("inheritance" in schema) ? schema.inheritance : [];
	eval(compiledQuery);
	var result = query(input)[0];
	var prefix = "";
	if ("output" in io)
		prefix = verify(result, io.output) ? "Equal to the expected result:\n" : "Differs from expected result:\n";
	document.getElementById("execresult").innerHTML = escapeHtml(prefix + JSON.stringify(result));
}
function executeButton() {
	var target = document.getElementById("target").value;
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
	for (var i=0; i<allresults.length; i++) {
		addResult(allresults[i].file,allresults[i].lang,allresults[i].value);
	}
}
function addResult(file,lang,value) {
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
	addOption(sel, "rule");
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
	addOption(sel, "spark_dataset");
	addOption(sel, "cloudant");
	document.getElementById("path").appendChild(li);
	return false;
}
function handleFile(files, output) {
	if (files.length > 0) {
		var reader = new FileReader();
		var file = files[0];
		if (file.name.endsWith(".sem")) {
			reader.onload = function(event) {
				var contents = btoa(String.fromCharCode.apply(null, new Uint8Array(event.target.result)))
				document.getElementById(output).innerHTML = contents;
			}
			reader.readAsArrayBuffer(file);
		} else {
			reader.onload = function(event) {
				var contents = escapeHtml(event.target.result);
				document.getElementById(output).innerHTML = contents;
			}																		
			reader.readAsText(file);
		}
	}
}
