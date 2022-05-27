/*
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

const { stringified } = require('./util');
const { qcertLib } = require('qcert-compiler');
const { QcertRunner } = require('qcert-runtime-js');

class Qcert {
  /* Build compilation configuration */
  static configure(source,queryName,schema,sourceQuery,output) {
    const config = {
      'qname' : queryName,
		  'source' : source,
		  'target' : 'js',
		  'exactpath' : false,
		  'emitall' : false,
		  'eval' : false,
		  'schema' : stringified(schema),
		  'input' : '{}', // Do not pass input, only compiling
      'output' : stringified(output),
		  'ascii' : true,
		  'javaimports' : '',
	    'optims' : '[]',
    };
    return qcertLib.buildConfig(config);
  }

  /* Call Q*cert compiler */
  static compile(source,queryName,schema,sourceQuery,output) {
    const gconf = Qcert.configure(source,queryName,schema,sourceQuery,output);
    const queryInput = {
      'gconf' : gconf,
		  'query' : sourceQuery,
    };
    const compileResult = qcertLib.compile(queryInput);
    if (compileResult.emit && compileResult.emit.value) {
      return { 'gconf' : gconf, 'result': compileResult.emit.value };
    } else {
      throw new Error(compileResult.result);
    }
  }

  /* validate result */
  static validate(gconf,queryName,source,output,result) {
    const config = {
		  'gconf' : gconf,
		  'source' : source,
		  'queryName' : queryName,
		  'actual' : stringified(result),
    };
    const valid = qcertLib.validateOutput(config);
    if (valid.error) {
      throw new Error(valid.error);
    } else {
      if (valid.result) {
        return `[${queryName} js] OK`;
      } else {
        const expected = stringified(output);
        const actual = stringified(valid.result);
        throw new Error (`[${queryName} js] ERROR\nExpected: ${expected}\nActual: ${actual}`);
      }
    }
  }

  /* run compiled query */
  static execute(schema,input,queryFile,compiledQuery,output,validate) {
    const queryName = queryFile.split('/').pop().split('.')[0];
    let result = QcertRunner.execute(schema,queryName,compiledQuery,input);
    if (validate) {
      if (output !== undefined) {
        const gconf = Qcert.configure('oql',queryName,schema,compiledQuery,output);
        return Qcert.validate(gconf,queryName,'js',output,result)
      } else {
        throw new Error('Cannot validate result without expected result (--output option)');
      }
    }
    return result;
  }

  /* compile query then execute */
  static compileExecute(source,schema,input,queryFile,sourceQuery,output,validate) {
    const queryName = queryFile.split('/').pop().split('.')[0];
    const compiledQuery = Qcert.compile(source,queryName,schema,sourceQuery,output);
    return Qcert.execute(schema,input,queryFile,compiledQuery.result,output,validate);
  }
}

module.exports = Qcert;
