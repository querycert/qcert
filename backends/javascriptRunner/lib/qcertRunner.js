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

class QcertRunner {
    /* Build compilation configuration */
    static configure(source,schema,sourceQuery,output) {
        const config = {
		        'source' : source,
		        'target' : 'js',
		        'exactpath' : false,
		        'emitall' : false,
		        'eval' : false,
		        'schema' : JSON.stringify(schema),
		        'input' : '{}', // Do not pass input, only compiling
            'output' : JSON.stringify(output),
		        'ascii' : true,
		        'javaimports' : '',
	          'optims' : '[]',
        };
        return QcertLib.buildConfig(config);
    }

    /* Call Q*cert compiler */
    static compile(source,schema,sourceQuery,output) {
        const gconf = QcertRunner.configure(source,schema,sourceQuery,output);
        const queryInput = {
            'gconf' : gconf,
		        'query' : sourceQuery,
        };
        const compileResult = QcertLib.compile(queryInput);
        if (compileResult.emit && compileResult.emit.value) {
            return { 'gconf' : gconf, 'result': compileResult.emit.value };
        } else {
            throw new Error(compileResult.result);
        }
    }

    /* Link compile query and load it as Node module */
    static loadQuery(schema,compiledQuery) {
        try {
            const inheritance = schema && schema.inheritance ? schema.inheritance : [];
            const inheritanceString = `const inheritance = ${JSON.stringify(inheritance)};`;
            const linkedQuery =
                  inheritanceString + QcertRuntimeString + compiledQuery + 'module.exports = { query };\n';
            const { query } = requireFromString(linkedQuery, 'query.js');
            return query;
        } catch(err) {
            Logger.error('Compiled query is not valid JavaScript');
            throw err;
        }
    }

    /* execute compiled query */
    static executeCompiled(schema,compiledQuery,input) {
        const query = QcertRunner.loadQuery(schema,compiledQuery);
        return query(input);
    }

    /* validate result */
    static validate(gconf,queryName,source,output,result) {
        const config = {
		        'gconf' : gconf,
		        'source' : source,
		        'queryName' : queryName,
		        'actual' : JSON.stringify(result),
        };
        const valid = QcertLib.validateOutput(config);
        if (valid.error) {
            throw new Error(valid.error);
        } else {
            if (valid.result) {
                return `[${queryName} js] OK`;
            } else {
                const expected = JSON.stringify(output);
                const actual = JSON.stringify(result);
                throw new Error (`[${queryName} js] ERROR\nExpected: ${expected}\nActual: ${actual}`);
            }
        }
    }

    /* compile query then execute */
    static compileExecute(source,schema,input,queryFile,sourceQuery,output,validate) {
        const compiledQuery = QcertRunner.compile(source,schema,sourceQuery,output);
        if (validate) {
            if (output) {
                let result = QcertRunner.executeCompiled(schema,compiledQuery.result,input);
                return QcertRunner.validate(compiledQuery.gconf,queryFile,source,output,result)
            } else {
                throw new Error('Cannot validate result without expected result (--output option)');
            }
        } else {
            return QcertRunner.executeCompiled(schema,compiledQuery.result,input);
        }
    }

    /* run compiled query */
    static execute(schema,input,queryFile,compiledQuery,output,validate) {
        const gconf = QcertRunner.configure('oql',schema,compiledQuery,output);
        if (validate) {
            if (output) {
                let result = QcertRunner.executeCompiled(schema,compiledQuery,input);
                return QcertRunner.validate(gconf,queryFile,'js',output,result)
            } else {
                throw new Error('Cannot validate result without expected result (--output option)');
            }
        } else {
            return QcertRunner.executeCompiled(schema,compiledQuery,input);
        }
    }
}

module.exports = QcertRunner;
