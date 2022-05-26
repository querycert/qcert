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

/* JavaScript runtime for ToString operators */

function toString(v) {
  return toStringQ(v, '');
}
function toText(v) {
  return toStringQ(v, '');
}
function toStringQ(v, quote) {
  if (v === null) {
    return 'null';
  }
  if (typeof v === 'object' && v.$coll && v.$length) {
    v = unboxColl(v);
  }
  const t = typeof v;
  if (t === 'string') {
    return quote + v + quote;
  }
  if (t === 'boolean') {
    return '' + v;
  }
  if (t === 'number') {
    if (Math.floor(v) === v) { return (new Number(v)).toFixed(1); } // Make sure there is always decimal point
    else { return '' + v; }
  }
  if (t === 'bigint') {
    return '' + v;
  }
  if ({}.toString.apply(v) === '[object Array]') {
    v = v.slice();
    v.sort();
    let result = '[';
    const n = v.length;
    for (let i = 0; i < n; i=i+1) {
      if (i > 0) {
        result += ', ';
      }
      result += toStringQ(v[i], quote);
    }
    return result + ']';
  }
  let result2 = '';
  if (v.$class) { // branded value
    let cl = v.$class;
    if (typeof cl === 'object' && cl.$coll && cl.$length) {
      cl = unboxColl(cl);
    }
    result2 += '<';
    result2 += cl;
    result2 += ':';
    result2 += toStringQ(v.$data, quote);
    result2 += '>';
  } else { // record
    // First need to sort
    const sortable = [];
    for (const key in v) {
      sortable.push({ key: key, val: v[key] });
    }
    sortable.sort(function(a, b) { return a.key.localeCompare(b.key); });
    result2 += '{';
    let first = true;
    const n = sortable.length;
    for (let i = 0; i < n; i=i+1) {
      if (first) { first = false; } else { result2 += ', '; }
      result2 += toStringQ(sortable[i].key, quote) + '->' + toStringQ(sortable[i].val, quote);
    }
    result2 += '}';
  }
  return result2 + '';
}
