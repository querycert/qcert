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

module.exports = { stringified, requireFromString };
