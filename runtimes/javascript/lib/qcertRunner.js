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

const getRuntime = require('./qcertRuntime');
const BoxedCollections = require('./boxedCollections');

/* Stringify */
function replacer(key, value) {
  if (typeof value === 'bigint') {
    return value.toString() + 'n';
  }
  return value;
}

function stringified(data) {
  if (typeof data === 'bigint') {
    return data.toString() + 'n';
  }
  return JSON.stringify(data, replacer);
}

/* Generic Node module require from string */
function requireFromString(src, filename) {
  const Module = module.constructor;
  const m = new Module();
  m._compile(src, filename);
  return m.exports;
}

class QcertRunner {
  /* Link compile query and load it as Node module */
  static loadQuery(schema,queryFile,compiledQuery) {
    try {
      const queryName = queryFile.split('/').pop().split('.')[0];
      const inheritance = schema && schema.inheritance ? schema.inheritance : [];
      const inheritanceString = `const inheritance = ${stringified(inheritance)};`;
      const QcertRuntimeString = getRuntime();
      const linkedQuery =
            inheritanceString + QcertRuntimeString + compiledQuery + `\nconst query = ${queryName};\nmodule.exports = { query };\n`;
      const { query } = requireFromString(linkedQuery, 'query.js');
      return query;
    } catch(err) {
      console.error('Compiled query is not valid JavaScript');
      throw err;
    }
  }

  /* run compiled query */
  static execute(schema,input,queryFile,compiledQuery) {
    const deserializedInput = BoxedCollections.boxColl(input);
    const query = QcertRunner.loadQuery(schema,queryFile,compiledQuery);
    /* This is actual execution */
    const deserializedOuput = query(input);
    const result = BoxedCollections.unboxColl(deserializedOuput);
    return result;
  }
}

module.exports = QcertRunner;
