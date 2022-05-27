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

class BoxedCollections {
  static boxColl(input) {
    let result = input;
    const t = typeof input;
    if ({}.toString.apply(input) === '[object Array]') {
      const coll = input.map(x => BoxedCollections.boxColl(x));
      result = {
        $coll: coll,
        $length: coll.length
      };
    } else if (typeof input === 'object') {
      if (Object.prototype.hasOwnProperty.call(input,'$nat')) {
        // Cannot convert a number with decimal point to BigInt
        result = BigInt(Math.floor(input.$nat));
      } else {
        for (const key in input) {
          input[key] = BoxedCollections.boxColl(input[key]);
        }
      }
    }
    return result;
  }
  static unboxColl(input) {
    let result = input;
    const t = typeof input;
    if (input && typeof input === 'bigint') {
      result = { $nat: Number(input) };
    } else if ({}.toString.apply(input) === '[object Array]') {
      result = input.map(x => BoxedCollections.unboxColl(x));
    } else if (input && typeof input === 'object') {
      if (Object.prototype.hasOwnProperty.call(input,'$coll')
          && Object.prototype.hasOwnProperty.call(input,'$length')) {
        result = BoxedCollections.unboxColl(input.$coll.slice(0,input.$length));
      } else {
        for (const key in input) {
          input[key] = BoxedCollections.unboxColl(input[key]);
        }
      }
    }
    return result;
  }
}

module.exports = BoxedCollections;
