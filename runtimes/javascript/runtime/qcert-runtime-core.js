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

/* JavaScript runtime for core operators */

/* Utilities */
function boxColl(v, len) {
  len = (typeof len !== 'undefined') ?  len : v.length;
  return { '$coll': v, '$length': len };
}
function unboxColl(v) {
  return v['$coll'];
}
function isBoxColl(obj) {
  return (Object.prototype.hasOwnProperty.call(obj,'$coll') &&
          Object.prototype.hasOwnProperty.call(obj,'$length'));
}
function collLength(v) {
  return v['$length'];
}
function boxLeft(v) {
  return { '$left' : v };
}
function unboxLeft(v) {
  return v['$left'];
}
function isLeft(v) {
  return Object.prototype.hasOwnProperty.call(v,'$left');
}
function boxRight(v) {
  return { '$right' : v };
}
function unboxRight(v) {
  return v['$right'];
}
function isRight(v) {
  return Object.prototype.hasOwnProperty.call(v,'$right');
}
function sub_brand(b1,b2) {
  let bsub = null;
  let bsup = null;
  const inheritanceUnbox = isBoxColl(inheritance) ? unboxColl(inheritance) : inheritance;
  const length = inheritanceUnbox.length;
  for (let i = 0; i < length; i=i+1) {
    bsub = inheritanceUnbox[i].sub;
    bsup = inheritanceUnbox[i].sup;
    if ((b1 === bsub) && (b2 === bsup)) { return true; }
  }
  return false;
}
// from: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions?redirectlocale=en-US&redirectslug=JavaScript%2FGuide%2FRegular_Expressions
function escapeRegExp(string){
  return string.replace(/([.*+?^=!:${}()|\[\]\/\\])/g, '\\$1');
}

/* Generic */
function equal(v1, v2) {
  return compare(v1, v2) === 0;
}
function compare(v1, v2) {
  const t1 = typeof v1;
  const t2 = typeof v2;
  if (t1 === 'object' && v1 !== null) {
    if (isBoxColl(v1)) {
	    v1 = unboxColl(v1).slice(0, collLength(v1));
	  }
  };
  if (t2 === 'object' && v2 !== null) {
    if (isBoxColl(v2)) {
	    v2 = unboxColl(v2).slice(0, collLength(v2));
	  }
  }
  if (t1 != t2) {
    return t1 < t2 ? -1 : +1;
  }
  const a1 = {}.toString.apply(v1);
  const a2 = {}.toString.apply(v2);
  if (a1 != a2) {
    return a1 < a2 ? -1 : +1;
  }
  if (a1 === '[object Array]') {
    v1 = v1.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    v2 = v2.slice(); /* So we do the sort/compare on a clone of the original array */
    v1.sort(compare);
    v2.sort(compare);
  }
  if (t1 === 'object') {
    const fields1 = [];
    const fields2 = [];
    for (const f1 in v1) { fields1.push(f1); }
    for (const f2 in v2) { fields2.push(f2); }
    fields1.sort(compare);
    fields2.sort(compare);
    for (let i = 0; i < fields1.length; i=i+1) {
      if (!(Object.prototype.hasOwnProperty.call(v2,fields1[i]))) {
        return -1;
      }
      const fc = compare(v1[fields1[i]], v2[fields1[i]]);
      if (fc != 0) {
        return fc;
      }
    }
    for (let i = 0; i < fields2.length; i=i+1) {
      if (!(Object.prototype.hasOwnProperty.call(v1,fields2[i]))) {
        return +1;
      }
    }
    return 0;
  }
  if (v1 != v2) {
    return v1 < v2 ? -1 : +1;
  }
  return 0;
}

/* Record */
function recConcat(r1, r2) {
  const result = { };
  for (const key2 in r2) {
    result[key2] = r2[key2];
  }
  for (const key1 in r1) {
    if (!(Object.prototype.hasOwnProperty.call(r2,key1))) {
      result[key1] = r1[key1];
    }
  }
  return result;
}
function recMerge(r1, r2) {
  const result = { };
  for (const key1 in r1) {
    result[key1] = r1[key1];
  }
  for (const key2 in r2) {
    if (Object.prototype.hasOwnProperty.call(r1,key2)) {
      if (!equal(r1[key2], r2[key2])) {
        return [ ];
      }
    } else {
      result[key2] = r2[key2];
    }
  }
  return [ result ];
}
function recRemove(r, f) {
  const result = { };
  for (let key in r) {
    if (key != f) {
      result[key] = r[key];
    }
  }
  return result;
}
function recProject(r1, p2) {
  const result = { };
  for (let key1 in r1) {
    if (!(p2.indexOf(key1) === -1)) {
      result[key1] = r1[key1];
    }
  }
  return result;
}
function recDot(receiver, member) {
  if (typeof receiver === 'object' && Object.prototype.hasOwnProperty.call(receiver,member)) {
    return receiver[member];
  }
  throw new Error('TypeError: recDot called on non-record');
}

/* Array */
function array(...args) {
  return boxColl(Array.of(...args));
}
function arrayLength(v) {
  return BigInt(v.$length);
}
function arrayPush(v1,v2) {
  const content1 = unboxColl(v1);
  if (content1.length !== collLength(v1)) {
	  content1 = content1.slice(0, collLength(length));
  }
  content1.push(v2);
  return boxColl(content1);
}
function arrayAccess(v1,v2) {
  const content1 = unboxColl(v1);
  return content1[v2];
}

/* Sum */
function either(v) {
  if (typeof v === 'object') {
    if (isLeft(v)) {
      return true;
    } else if (isRight(v)) {
      return false;
    } else {
      throw new Error('TypeError: either called on non-sum');
    }
  }
  throw new Error('TypeError: either called on non-sum');
}
function getLeft(v) {
  if (typeof v === 'object' && isLeft(v)) {
    return unboxLeft(v);
  }
  throw new Error('TypeError: getLeft called on non-sum');
}
function getRight(v) {
  if (typeof v === 'object' && isRight(v)) {
    return unboxRight(v);
  }
  throw new Error('TypeError: getRight called on non-sum');
}

/* Brand */
function unbrand(v) {
  if (typeof v === 'object' && Object.prototype.hasOwnProperty.call(v,'$class') && Object.prototype.hasOwnProperty.call(v,'$data')) {
    return v.$data;
  }
  throw new Error('TypeError: unbrand called on non-object');
}
function cast(brands,v) {
  const brandsUnbox = isBoxColl(brands) ? unboxColl(brands) : brands;
  const type = isBoxColl(v.$class) ? unboxColl(v.$class) : v.$class;
  if (brandsUnbox.length === 1 && brandsUnbox[0] === 'Any') { /* cast to top of inheritance is built-in */
    return boxLeft(v);
  }
  brands:
  for (const i in brandsUnbox) {
    const b = brandsUnbox[i];
    for (const j in type) {
      const t = type[j];
      if (equal(t,b) || sub_brand(t,b)) {
        continue brands;
      }
    }
    /* the brand b does not appear in the type, so the cast fails */
    return boxRight(null);
  }
  /* All brands appear in the type, so the cast succeeds */
  return boxLeft(v);
}

/* Collection */
function iterColl(b, f) {
  const content = unboxColl(b);
  for (let i = 0; i < collLength(b); i=i+1) {
	  f(content[i]);
  }
}
function distinct(b) {
  const result = [ ];
  const content = unboxColl(b);
  for (let i = 0; i < collLength(b); i=i+1) {
    const v = content[i];
    let dup = false;
    for (let j = i+1; j < collLength(b); j=j+1) {
      if (equal(v,content[j])) { dup = true; break; }
    }
    if (!(dup)) { result.push(v); } else { dup = false; }
  }
  return boxColl(result);
}
function singleton(v) {
  const content = unboxColl(v);
  if (collLength(v) === 1) {
    return boxLeft(content[0]);
  } else {
    return boxRight(null); /* Not a singleton */
  }
}
function flatten(aOuter) {
  const result = [ ];
  const aOuterContent = unboxColl(aOuter);
  const nOuter = collLength(aOuter);
  for (let iOuter = 0; iOuter < nOuter; iOuter = iOuter+1) {
    const aInner = aOuterContent[iOuter];
    const aInnerContent = unboxColl(aInner);
    const nInner = collLength(aInner);
    for (let iInner = 0; iInner < nInner; iInner = iInner+1) {
      result.push(aInnerContent[iInner]);
    }
  }
  return boxColl(result);
}
function union(b1, b2) {
  let content1 = unboxColl(b1);
  let content2 = unboxColl(b2);
  if (content1.length !== collLength(b1)) {
	  content1 = content1.slice(0, collLength(b1));
  }
  const length2 = collLength(b2);
  for (let i = 0; i < length2; i=i+1) {
    content1.push(content2[i]);
  }
  return boxColl(content1);
}
function minus(b1, b2) {
  const result = [ ];
  const v1 = unboxColl(b1).slice(0, collLength(b1));
  const v2 = unboxColl(b2).slice(0, collLength(b2));
  v1.sort(compare);
  v2.sort(compare);
  let i2 = 0;
  const length2 = v2.length;
  for (let i1 = 0; i1 < v1.length; i1=i1+1) {
    while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) {
      i2 = i2+1;
    }
    if (i2 < length2) {
      if (compare(v1[i1],v2[i2]) === (-1)) { result.push(v1[i1]); } else { i2=i2+1; }
    } else {
      result.push(v1[i1]);
    }
  }
  return boxColl(result);
}
function min(b1, b2) {
  const result = [ ];
  const v1 = unboxColl(b1).slice(0, collLength(b1));
  const v2 = unboxColl(b2).slice(0, collLength(b2));
  v1.sort(compare);
  v2.sort(compare);
  let i2 = 0;
  const length2=v2.length;
  for (let i1 = 0; i1 < v1.length; i1=i1+1) {
    while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) {
      i2=i2+1;
    }
    if (i2 < length2) {
      if (compare(v1[i1],v2[i2]) === 0) result.push(v1[i1]);
    }
  }
  return boxColl(result);
}
function max(b1, b2) {
  const result = [ ];
  const v1 = unboxColl(b1).slice(0, collLength(b1));
  const v2 = unboxColl(b2).slice(0, collLength(b2));
  v1.sort(compare);
  v2.sort(compare);
  let i2 = 0;
  const length2 = v2.length;
  for (let i1 = 0; i1 < v1.length; i1=i1+1) {
    while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) {
      result.push(v2[i2]); i2=i2+1;
    }
    if (i2 < length2) {
      if (compare(v1[i1],v2[i2]) === 0) i2=i2+1;
    }
    result.push(v1[i1]);
  }
  while (i2 < length2) { result.push(v2[i2]); i2 = i2+1; }
  return boxColl(result);
}
function nth(b1, n) {
  const index = n;
  const content = unboxColl(b1);
  if (0 <= index && index < collLength(b1)) {
    return boxLeft(content[index]);
  } else {
    return boxRight(null);
  }
}
function count(v) {
  return arrayLength(v);
}
function contains(v, b) {
  const content = unboxColl(b);
  for (let i = 0; i < collLength(b); i=i+1) {
    if (equal(v, content[i])) {
      return true;
    }
  }
  return false;
}
function compareOfMultipleCriterias(scl) {
  const criterias = unboxColl(scl);
  return function(a,b) {
    let current_compare = 0;
    for (let i = 0; i < criterias.length; i=i+1) {
      const sc = criterias[i];
      if (Object.prototype.hasOwnProperty.call(sc,'asc')) {
          current_compare = compare(recDot(a,sc['asc']), recDot(b,sc['asc']));
      }
      else if (Object.prototype.hasOwnProperty.call(sc,'desc')) {
        current_compare = -(compare(recDot(a,sc['asc']), recDot(b,sc['asc'])));
      }

      if (current_compare === -1) { return -1; }
      else if (current_compare === 1) { return 1; }
    }
    return current_compare;
  }
}
function sort(scl,b) {
  if (scl.length === 0) { return b; } // Check for no sorting criteria
  const compareFun = compareOfMultipleCriterias(scl);
  /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
  const result = unboxColl(b).slice(0, collLength(b));
  result.sort(compareFun);
  return boxColl(result);
}
function groupByOfKey(l,k,keysf) {
  const result = [ ];
  l.forEach((x) => {
    if (equal(keysf(x),k)) {
      result.push(x);
    }
  });
  return boxColl(result);
}
function groupByNested(l,keysf) {
  const keys = unboxColl(distinct(boxColl(l.map(keysf))));
  const result = [ ];
  keys.forEach((k) => {
    result.push({ 'keys': k, 'group' : groupByOfKey(l,k,keysf) });
  });
  return result;
}
function groupBy(g,kl,l) {
  l = unboxColl(l).slice(0, collLength(l));
  kl = unboxColl(kl).slice(0, collLength(kl));
  // g is partition name
  // kl is key list
  // l is input collection of records
  const keysf = function (j) {
    return recProject(j,kl);
  };
  const grouped = groupByNested(l,keysf);
  const result = [ ];
  grouped.forEach((x) => {
    const gRec = {};
    gRec[g] = x.group;
    result.push(recConcat(x.keys, gRec));
  });
  return boxColl(result);
}

/* String */
function length(v) {
  return BigInt(v.length);
}
function substring(v, start, len) {
  return v.substring(Number(start),Number(len));
}
function substringEnd(v, start) {
  return v.substring(Number(start));
}
function stringJoin(sep, v) {
  const content = unboxColl(v).slice(0, collLength(v));
  return content.join(sep);
}
function like(pat, s) {
  const reg1 = escapeRegExp(pat);
  const reg2 = reg1.replace(/_/g, '.').replace(/%/g, '.*');
  const reg3 = new RegExp(reg2);
  return reg3.test(s);
}

/* Integer */
function natLt(v1, v2) {
  return v1 < v2;
}
function natLe(v1, v2) {
  return v1 <= v2;
}
function natPlus(v1, v2) {
  return v1 + v2;
}
function natMinus(v1, v2) {
  return v1 - v2;
}
function natMult(v1, v2) {
  return v1 * v2;
}
function natDiv(v1, v2) {
  return v1 / v2;
}
function natRem(v1, v2) {
  return v1 % v2;
}
function natAbs(v) {
  return v >= 0n ? v : -v;
}
function natLog2(v) {
  // XXX We likely could do something better
  return BigInt(Math.floor(Math.log2(Number(v)))); // Default Z.log2 is log_inf, biggest integer lower than log2
}
function natSqrt(v) {
  return BigInt(Math.floor(Math.sqrt(Number(v)))); // See Z.sqrt biggest integer lower than sqrt
}
function natMinPair(v1, v2) {
  return v1 < v2 ? v1 : v2;
}
function natMaxPair(v1, v2) {
  return v2 < v1 ? v1 : v2;
}
function natSum(b) {
  const content = unboxColl(b);
  let result = 0n;
  for (let i = 0; i < collLength(b); i=i+1) {
    result += content[i];
  }
  return result;
}
function natMin(b) {
  const content = unboxColl(b);
  let result = content[0] || 0;
  for (let i = 0; i < collLength(b); i=i+1) {
    if (content[i] < result) {
      result = content[i];
    }
  }
  return result;
}
function natMax(b) {
  const content = unboxColl(b);
  let result = content[0] || 0;
  for (let i = 0; i < collLength(b); i=i+1) {
    if (content[i] > result) {
      result = content[i];
    }
  }
  return result;
}
function natArithMean(b) {
  const len = collLength(b);
  if (len === 0) {
    return 0n;
  } else {
    return natSum(b)/BigInt(len);
  }
}
function floatOfNat(v) {
  return Number(v);
}

/* Float */
function floatSum(b) {
  const content = unboxColl(b);
  let result = 0;
  for (let i = 0; i < collLength(b); i=i+1) {
    result += content[i];
  }
  return result;
}
function floatArithMean(b) {
  const len = collLength(b);
  if (len === 0) {
    return 0;
  } else {
    return floatSum(b)/len;
  }
}
function floatMin(b) {
  const content = unboxColl(b).slice(0, collLength(b));
  return Math.min.apply(Math,content);
}
function floatMax(b) {
  const content = unboxColl(b).slice(0, collLength(b));
  return Math.max.apply(Math,content);
}
function natOfFloat(v) {
  return boxNat(Math.trunc(v));
}
