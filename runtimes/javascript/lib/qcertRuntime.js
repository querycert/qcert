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

const Fs = require('fs');
const Path = require('path');
const QcertRuntimeCore = Fs.readFileSync(Path.join(__dirname,'../runtime/qcert-runtime-core.js'),'utf8');
const QcertRuntimeToString = Fs.readFileSync(Path.join(__dirname,'../runtime/qcert-runtime-tostring.js'),'utf8');
const QcertRuntimeSqlDate = Fs.readFileSync(Path.join(__dirname,'../runtime/qcert-runtime-sql-date.js'),'utf8');
const QcertRuntimeUri = Fs.readFileSync(Path.join(__dirname,'../runtime/qcert-runtime-uri.js'),'utf8');

function getRuntime() {
  return QcertRuntimeCore
    + QcertRuntimeSqlDate
    + QcertRuntimeToString
    + QcertRuntimeUri;
}

module.exports = getRuntime;
