let url = 'https://openwhisk.ng.bluemix.net/api/v1/web/simeon@us.ibm.com_dev/qcert/cloudant-compile-deploy.json'

const compileAndDeployButton = () => {
  const input = {
    'cloudant': {
      'username': getParameter('cloudant-username', ''),
      'password': getParameter('cloudant-password', '')
    },
    'whisk': {
      'api_key': getParameter('wsk-api_key', ''),
      'namespace': getParameter('wsk-namespace', ''),
      'api_host' : getParameter('wsk-api_host', ''),
    },
    'pkgname': getParameter('wsk-pkg', ''),
    'source': getParameter("source", ""),
    'exactpath': getParameter("exactpath", "FillPath") === "ExactPath",
    'emitall': getParameter("emitall", "EmitTarget") === "EmitAll",
    'eval': false,
    'input': getParameter("input", "{}"),
    'ascii': getParameter("charset", "Greek") === "Ascii",
    'javaimports': getParameter("java_imports", ""),
    'query': document.getElementById("query").value,
    'optims': getParameter("optim", "[]")
  };

  const resultLoading = '<h3>Result</h3> <div class="loader"></div>'
  document.getElementById("result").innerHTML = resultLoading;
  const success = function (result) {
    console.log('result = ', JSON.stringify(result));
    const resultUrl = 'https://openwhisk.ng.bluemix.net/api/v1/web/' +
      input.whisk.namespace + '/' + input.pkgname + '/result.json'
    const undeployUrl = 'https://openwhisk.ng.bluemix.net/api/v1/web/' +
      input.whisk.namespace + '/' + input.pkgname + '/undeploy.json'
    const readResultFunc =
      makeHandler('{}', resultUrl,
        (res) => {
          document.getElementById("resultValue").innerHTML = JSON.stringify(res.result)
        },
        () => {
          document.getElementById("resultValue").innerHTML = 'error'
        })
    const readResultInterval = setInterval(readResultFunc, 1000)
    undeployButton = () => {
      clearInterval(readResultInterval)
      const undeploy = makeHandler('{}', undeployUrl,
        (res) => {
          console.log('undeployed')
          document.getElementById("result").innerHTML = ''
        },
        () => {
          console.log('undeployed failed')
          undeployButton = () => {
            console.log('already undeploy!')
          }
        })
      undeploy()
    }
    const resultText =
      '<h3>Result</h3>\n' +
      '<div class="form-group">\n' +
      '  <label class="control-label col-sm-2" for="result-value">result:</label>\n' +
      '  <pre id=resultValue></pre>' +
      '</div>\n' +
      '<h3>Deployment</h3>\n' +
      '<div class="form-group">\n' +
      '  <label class="control-label col-sm-2" for="result-url">result:</label>\n' +
      '  <div class="col-sm-10">\n' +
      '    <pre><a href="' + resultUrl + '">' + resultUrl + '</a></pre>' + '\n' +
      '  </div>\n' +
      '</div>\n' +
      '<div class="form-group">\n' +
      '  <label class="control-label col-sm-2" for="undeploy-url">undeploy:</label>\n' +
      '  <div class="col-sm-10">\n' +
      '    <pre><a href="' + undeployUrl + '">' + undeployUrl + '</a></pre>\n' +
      '  </div>\n' +
      '</div>\n' +
      '<div class="form-group text-right">\n' +
      '  <button type="button" onclick="undeployButton()" class="btn btn-primary">undeploy</button>\n' +
      '</div>\n'
    document.getElementById("result").innerHTML = resultText

  }
  const failure = (msg) => {
    document.getElementById("result").innerHTML = msg;
  }
  const call = makeHandler(input, url, success, failure)
  call()
}

let undeployButton = () => {
  console.log('undeploy not yet defined!')
}

const makeHandler = (input, url, success, failure) => {
  return function () {
    console.log("Handler invoked on URL " + url);
    const request = new XMLHttpRequest();
    request.open("POST", url, true);
    request.setRequestHeader("Content-Type", "application/json");
    request.onloadend = function () {
	if (request.status == 200) {
            console.log("Success at url " + url);
	    const response = JSON.parse(request.response);
	    if (response.hasOwnProperty('message')) { failure(response.message); }
	    else { success(response); }
	}
	else {
            console.log("Failure at url " + url);
            failure("compilation or deployment failed");
	}
    };
      try {
	  console.log("Posting request on url " + url);
	  request.send(JSON.stringify(input));
      } catch (e) {
      }
  };
}

const entityMap = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': '&quot;',
  "'": '&#39;',
  "/": '&#x2F;'
}

const escapeHtml = (string) => {
  return String(string).replace(/[&<>"'\/]/g, function (s) {
    return entityMap[s];
  });
}

const getParameter = (paramName, defaultValue) => {
  elem = document.getElementById(paramName);
  if (elem != null) {
    return elem.value;
  } else {
    return defaultValue;
  }
}
