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
const QcertRunner = require('./qcertRunner');

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
     * Compile and execute query
     *
     * @param {string} source - source language
     * @param {string} schemaFile - schema file
     * @param {string} queryFile - query file
     * @param {string} inputFile - input data file
     * @param {string} outputFile - expected result file
     * @param {boolean} validate - validate the result
     * @returns {object} Promise to the result of execution
     */
    static execute(source,schemaFile,queryFile,inputFile,outputFile,validate) {
        const input = getJson(inputFile);
        const sourceQuery = Fs.readFileSync(queryFile,'utf8');
        const schema = getJson(schemaFile);
        const output = outputFile ? getJson(outputFile) : null;
        return QcertRunner.compileExecute(source,schema,input,queryFile,sourceQuery,output,validate);
    }

}

module.exports = Commands;
