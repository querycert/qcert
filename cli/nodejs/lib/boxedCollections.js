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
        var t = typeof input;
        if ({}.toString.apply(input) === '[object Array]') {
            input.forEach(x => BoxedCollections.boxColl(x));
            result = {
                $coll: input,
                $length: input.length
            };
        } else if (typeof input === 'object') {
            for (var key in input) {
                input[key] = BoxedCollections.boxColl(input[key]);
            }
        }
        return result;
    }
    static unboxColl(input) {
        let result = input;
        var t = typeof input;
        if ({}.toString.apply(input) === '[object Array]') {
            input.forEach(x => BoxedCollections.unboxColl(x));
        } else if (typeof input === 'object') {
            if (Object.prototype.hasOwnProperty.call(input,'$coll')
                && Object.prototype.hasOwnProperty.call(input,'$length')) {
                result = BoxedCollections.unboxColl(input.$coll.slice(0,input.$length));
            } else {
                for (var key in input) {
                    input[key] = BoxedCollections.unboxColl(input[key]);
                }
            }
        }
        return result;
    }
}

module.exports = BoxedCollections;
