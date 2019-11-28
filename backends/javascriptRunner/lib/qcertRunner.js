/*
 * Copyright 2017 IBM Corporation
 *
 * Licensed under the Apache License; Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing; software
 * distributed under the License is distributed on an "AS IS" BASIS;
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND; either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

const Fs = require('fs');
const Path = require('path');
const Logger = require('./logger');
const QcertLib = require('./qcertLib');
const QcertRuntimeString = Fs.readFileSync(Path.join(__dirname,'../extracted/qcert-runtime.js'),'utf8');

/* Generic Node module require from string */
function requireFromString(src, filename) {
  var Module = module.constructor;
  var m = new Module();
  m._compile(src, filename);
  return m.exports;
}

/* Call Q*cert compiler */
function compile(source,schema,sourceQuery) {
    const config = {
		    'source' : source,
		    'target' : 'js',
		    'exactpath' : false,
		    'emitall' : false,
		    'eval' : false,
		    'schema' : JSON.stringify(schema),
		    'input' : '{}', // Do not pass input, only compiling
		    'ascii' : true,
		    'javaimports' : '',
		    'query' : sourceQuery,
	      'optims' : '[]',
    };
    const compileResult = QcertLib.compile(config);
    if (compileResult.emit && compileResult.emit.value) {
        return compileResult.emit.value;
    } else {
        throw new Error(compileResult.result);
    }
}

/* Link compile query and load it as Node module */
function loadQuery(compiledQuery) {
    try {
        const linkedQuery = QcertRuntimeString + compiledQuery + 'module.exports = { query };\n';
        const { query } = requireFromString(linkedQuery, 'query.js');
        return query;
    } catch(err) {
        Logger.error('Compiled query is not valid JavaScript');
        throw err;
    }
}

/* execute compiled query */
function execute(compiledQuery,input) {
    const query = loadQuery(compiledQuery);
    return query(input);
}

/* compile query then execute */
function compileExecute(source,schema,input,sourceQuery) {
    const compiledQuery = compile(source,schema,sourceQuery);
    return execute(compiledQuery,input);
}

module.exports = { compile, execute, compileExecute };
