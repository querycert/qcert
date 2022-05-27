/*
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

'use strict';

const Fs = require('fs');
const { stringified } = require('../lib/util');
const Qcert = require('./Qcert');

/**
 * Load a file or JSON string
 *
 * @param {object} input either a file name or a json string
 * @return {object} JSON object
 */
function getJson(input) {
  let jsonString;
  if (input.file) {
    jsonString = Fs.readFileSync(input.file, 'utf8');
  } else {
    jsonString = input.content;
  }
  return JSON.parse(jsonString);
}

/**
 * Utility class that implements the commands exposed by the Qcert CLI.
 * @class
 */
class Commands {
  /**
   * Compile and run query
   *
   * @param {string} source - source language
   * @param {string} schemaFile - schema file
   * @param {string} queryFile - query file
   * @param {string} inputFile - input data file
   * @param {string} outputFile - expected result file
   * @param {boolean} validate - validate the result
   * @returns {object} Promise to the result of execution
   */
  static compile(source,schemaFile,queryFile,inputFile,outputFile,validate) {
    const input = getJson(inputFile);
    const sourceQuery = Fs.readFileSync(queryFile,'utf8');
    const schema = getJson(schemaFile);
    const output = outputFile ? getJson(outputFile) : null;
    const result = Qcert.compileExecute(source,schema,input,queryFile,sourceQuery,output,validate);
    if (validate) {
      return result;
    } else {
      return stringified(result);
    }
  }

  /**
   * Run query
   *
   * @param {string} schemaFile - schema file
   * @param {string} queryFile - compiled query file
   * @param {string} inputFile - input data file
   * @param {string} outputFile - expected result file
   * @param {boolean} validate - validate the result
   * @returns {object} Promise to the result of execution
   */
  static execute(schemaFile,queryFile,inputFile,outputFile,validate) {
    const input = getJson(inputFile);
    const sourceQuery = Fs.readFileSync(queryFile,'utf8');
    const schema = getJson(schemaFile);
    const output = outputFile ? getJson(outputFile) : null;
    const result = Qcert.execute(schema,input,queryFile,sourceQuery,output,validate);
    if (validate) {
      return result;
    } else {
      return stringified(result);
    }
  }

}

module.exports = Commands;
