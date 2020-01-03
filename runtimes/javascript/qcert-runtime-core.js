/*
 * Copyright 2015-2016 IBM Corporation
 *
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

/* "standard library" (implementation of unary and binary operators) */
/* XXX TODO
   -- never use 'in' always use 'hasObjectProperty()' instead
   -- never use '==' or '!=' always use '===' or '!==' instead
   -- never use 'i++' always use 'i = i+1'
*/

/* Utilities */
function mustBeArray(obj) {
    if (Array.isArray(obj)) {
	      return;
    }
    throw "Expected an array but got: " + JSON.stringify(obj);
}
function mkLeft(v) {
    return { "$left" : v };
}
function mkRight(v) {
    return { "$right" : v };
}
function sub_brand(b1,b2) {
    var bsub=null;
    var bsup=null;
    for (var i=0; i<inheritance.length; i++) {
	      bsub = inheritance[i].sub;
	      bsup = inheritance[i].sup;
	      if ((b1 == bsub) && (b2 == bsup)) return true;
    }
    return false;
}
function mkWorld(v) {
    return { "WORLD" : v };
}

/* Generic */
function equal(v1, v2) {
    return compare(v1, v2) == 0;
}
function compare(v1, v2) {
    var t1 = typeof v1, t2 = typeof v2;
    if (t1 == "object" && v1 !== null) {
        if (v1.hasOwnProperty('$nat')) { t1 = "number"; v1 = v1.$nat; }
    };
    if (t2 == "object" && v2 !== null) {
        if (v2.hasOwnProperty('$nat')) { t2 = "number"; v2 = v2.$nat; }
    };
    if (t1 != t2)
        return t1 < t2 ? -1 : +1;
    var a1 = {}.toString.apply(v1), a2 = {}.toString.apply(v2);
    if (a1 != a2)
        return a1 < a2 ? -1 : +1;
    if (a1 == "[object Array]") {
	      v1 = v1.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
	      v2 = v2.slice(); /* So we do the sort/compare on a clone of the original array */
        v1.sort(compare);
        v2.sort(compare);
    }
    if (t1 == "object") {
	      var fields1 = [];
	      var fields2 = [];
	      for (var f1 in v1) { fields1.push(f1); }
	      for (var f2 in v2) { fields2.push(f2); }
	      fields1 = fields1.sort(compare);
	      fields2 = fields2.sort(compare);
        for (var i = 0; i < fields1.length; i++) {
            if (!(fields1[i] in v2))
                return -1;
            var fc = compare(v1[fields1[i]], v2[fields1[i]]);
            if (fc != 0)
                return fc;
        }
	      for (var i = 0; i < fields2.length; i++) {
            if (!(fields2[i] in v1))
                return +1;
	      }
        return 0;
    }
    if (v1 != v2)
        return v1 < v2 ? -1 : +1;
    return 0;
}
function toString(v) {
    return toStringQ(v, "");
}
function toText(v) {
    return toStringQ(v, "");
}
function toStringQ(v, quote) {
    if (v === null)
	      return "null";
    var t = typeof v;
    if (t == "string")
	      return quote + v + quote;
    if (t == "boolean")
	      return "" + v;
    if (t == "number") {
	      if (Math.floor(v) == v) return (new Number(v)).toFixed(1); // Make sure there is always decimal point
	      else return "" + v;
    }
    if ({}.toString.apply(v) == "[object Array]") {
	      v = v.slice();
	      v.sort();
	      var result = "[";
	      for (var i=0, n=v.length; i<n; i++) {
	          if (i > 0)
		            result += ", ";
	          result += toStringQ(v[i], quote);
	      }
	      return result + "]";
    }
    if(v.hasOwnProperty('$nat')){
	      return "" + v.$nat;
    }
    var result2 = "";
    if (v.$class) { // branded value
        result2 += "<";
        result2 += v.$class;
        result2 += ":";
        result2 += toStringQ(v.$data, quote);
        result2 += ">";
    } else { // record
        // First need to sort
        var sortable = [];
        for (var key in v) {
            sortable.push({ key: key, val: v[key] });
        }
        sortable.sort(function(a, b) { return a.key.localeCompare(b.key); });
        var result2 = "{";
        var first = true;
        for (var i=0, n=sortable.length; i<n; i++) {
	          if (first) first = false; else result2 += ", ";
	          result2 += toStringQ(sortable[i].key, quote) + "->" + toStringQ(sortable[i].val, quote);
        }
        result2 += "}";
    }
    return result2 + "";
}

/* Record */
function recConcat(r1, r2) {
    var result = { };
    for (var key2 in r2)
        result[key2] = r2[key2];
    for (var key1 in r1)
        if (!(key1 in r2))
            result[key1] = r1[key1];
    return result;
}
function recMerge(r1, r2) {
    var result = { };
    for (var key1 in r1)
	      result[key1] = r1[key1];
    for (var key2 in r2) {
	      if (key2 in r1) {
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
    var result = { };
    for (var key in r)
	      if (key != f)
	          result[key] = r[key];
    return result;
}
function recProject(r1, p2) {
    var result = { };
    for (var key1 in r1) {
	      if (!(p2.indexOf(key1) == -1))
            result[key1] = r1[key1];
    }
    return result;
}
function recDot(receiver, member) {
    if (typeof receiver === "object" && member in receiver) {
	      return receiver[member];
    }
    throw "TypeError: recDot called on non-record";
}

/* Sum */
function either(v) {
    if (typeof v === "object")
        if ("$left" in v) {
            return true;
        } else if ("$right" in v) {
            return false;
        } else {
            throw "TypeError: either called on non-sum";
        }
    throw "TypeError: either called on non-sum";
}
function toLeft(v) {
    if (typeof v === "object" && "$left" in v) {
	      return v.$left;
    }
    throw "TypeError: toLeft called on non-sum";
}
function toRight(v) {
    if (typeof v === "object" && "$right" in v) {
	      return v.$right;
    }
    throw "TypeError: toRight called on non-sum";
}

/* Brand */
function brand(b,v) {
    return { "$class" : b, "$data" : v };
}
function unbrand(v) {
    if (typeof v === "object" && "$class" in v && "$data" in v) {
	      return v.$data;
    }
    throw "TypeError: unbrand called on non-object";
}
function cast(brands,v) {
    mustBeArray(brands);
    var type = v.$class;
    mustBeArray(type);
    if (brands.length == 1 && brands[0] == "Any") { /* cast to top of inheritance is built-in */
    	  return mkLeft(v);
    }
    brands:
    for (var i in brands) {
	      var b = brands[i];
    	  for (var j in type) {
    	      var t = type[j];
    	      if (equal(t,b) || sub_brand(t,b))
    		        continue brands;
    	  }
    	  /* the brand b does not appear in the type, so the cast fails */
    	  return mkRight(null);
    }
    /* All brands appear in the type, so the cast succeeds */
    return mkLeft(v);
}

/* Collection */
function distinct(b) {
    var result = [ ];
    for (var i=0; i<b.length; i++) {
        var v = b[i];
        var dup = false;
        for (var j=0; j<result.length;j++) {
            if (equal(v,result[j])) { dup = true; break; }
        }
        if (!(dup)) { result.push(v); } else { dup = false; }
    }
    return result;
}
function singleton(v) {
    if (v.length == 1) {
	      return mkLeft(v[0]);
    } else {
	      return mkRight(null); /* Not a singleton */
    }
}
function flatten(aOuter) {
    var result = [ ];
    for (var iOuter=0, nOuter=aOuter.length; iOuter<nOuter; iOuter++) {
	      var aInner = aOuter[iOuter];
	      for (var iInner=0, nInner=aInner.length; iInner<nInner; iInner++)
	          result.push(aInner[iInner]);
    }
    return result;
}
function union(b1, b2) {
    var result = [ ];
    for (var i1=0; i1<b1.length; i1++)
	      result.push(b1[i1]);
    for (var i2=0; i2<b2.length; i2++)
	      result.push(b2[i2]);
    return result;
}
function minus(b1, b2) {
    var result = [ ];
    var v1 = b1.slice();
    var v2 = b2.slice();
    v1.sort(compare);
    v2.sort(compare);
    var i2=0;
    var length2=v2.length;
    var comp=0;
    for (var i1=0; i1<v1.length; i1++) {
	      while ((i2 < length2) && (compare(v1[i1],v2[i2]) == 1)) i2++;
	      if (i2 < length2) {
	          if(compare(v1[i1],v2[i2]) == (-1)) { result.push(v1[i1]); } else { i2++; }
	      } else {
	          result.push(v1[i1]);
	      }
    }
    return result;
}
function min(b1, b2) {
    var result = [ ];
    var v1 = b1.slice();
    var v2 = b2.slice();
    v1.sort(compare);
    v2.sort(compare);
    var i2=0;
    var length2=v2.length;
    var comp=0;
    for (var i1=0; i1<v1.length; i1++) {
	      while ((i2 < length2) && (compare(v1[i1],v2[i2]) == 1)) i2++;
	      if (i2 < length2) {
	          if(compare(v1[i1],v2[i2]) == 0) result.push(v1[i1]);
	      }
    }
    return result;
}
function max(b1, b2) {
    var result = [ ];
    var v1 = b1.slice();
    var v2 = b2.slice();
    v1.sort(compare);
    v2.sort(compare);
    var i2=0;
    var length2=v2.length;
    var comp=0;
    for (var i1=0; i1<v1.length; i1++) {
	      while ((i2 < length2) && (compare(v1[i1],v2[i2]) == 1)) { result.push(v2[i2]); i2++; }
	      if (i2 < length2) {
	          if(compare(v1[i1],v2[i2]) == 0) i2++;
	      }
	      result.push(v1[i1]);
    }
    while (i2 < length2) { result.push(v2[i2]); i2++; }
    return result;
}
function nth(b1, n) {
    var index = n;
    if(n.hasOwnProperty('$nat')){
	      index = n.$nat;
    }
    if (b1[index]) {
        return mkLeft(b1[index]);
    } else {
        return mkRight(null);
    }
}
function count(v) {
    return { "$nat" : v.length };
}
function contains(v, b) {
    for (var i=0; i<b.length; i++)
	      if (equal(v, toLeft(b[i])))
	          return true;
    return false;
}
function compareOfMultipleCriterias(scl) {
    return function(a,b) {
	      var current_compare = 0;
	      for (var i=0; i<scl.length; i++) {
	          var sc = scl[i];
	          if ("asc" in sc) { current_compare = compare(recDot(a,sc['asc']), recDot(b,sc['asc'])); }
	          else if ("desc" in sc) { current_compare = -(compare(recDot(a,sc['asc']), recDot(b,sc['asc']))); }

	          if (current_compare == -1) { return -1; }
	          else if(current_compare == 1) { return 1; }
	      }
	      return current_compare;
    }
    
}
function sort(b,scl) {
    var result = [ ];
    if (scl.length == 0) { return b; } // Check for no sorting criteria
    var compareFun = compareOfMultipleCriterias(scl);
    result = b.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    result.sort(compareFun);
    return result;
}
function groupBy(l) { // Not implemented
    throw "groupBy not implemented";
}

/* String */
function length(v) {
    return { "$nat" : v.length };
}
function substring(v, start, len) {
    return v.substring(start.$nat,len.$nat);
}
function substringEnd(v, start) {
    return v.substring(start.$nat);
}
function stringJoin(sep, v) {
    return v.join(sep);
}

/* Integer */
function natPlus(v1, v2) {
    return { "$nat" : v1.$nat + v2.$nat };
}
function natMinus(v1, v2) {
    return { "$nat" : v1.$nat - v2.$nat };
}
function natMult(v1, v2) {
    return { "$nat" : v1.$nat * v2.$nat };
}
function natDiv(v1, v2) {
    return { "$nat" : Math.floor(v1.$nat / v2.$nat) };
}
function natRem(v1, v2) {
    return { "$nat" : Math.floor(v1.$nat % v2.$nat) };
}
function natAbs(v) {
    return { "$nat" : Math.abs(v.$nat) };
}
function natLog2(v) {
    return { "$nat" : Math.floor(Math.log2(v.$nat)) }; // Default Z.log2 is log_inf, biggest integer lower than log2
}
function natSqrt(v) {
    return { "$nat" : Math.floor(Math.sqrt(v.$nat)) }; // See Z.sqrt biggest integer lower than sqrt
}
function natMinPair(v1, v2) {
    return { "$nat" : Math.min(v1.$nat,v2.$nat) };
}
function natMaxPair(v1, v2) {
    return { "$nat" : Math.max(v1.$nat,v2.$nat) };
}
function natSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i++)
	      result += b[i].$nat;
    return { "$nat" : result };
}
function natMin(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i++)
	      numbers.push(b[i].$nat);
    return { "$nat" : Math.min.apply(Math,numbers) };
}
function natMax(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i++)
	      numbers.push(b[i].$nat);
    return { "$nat" : Math.max.apply(Math,numbers) };
}
function natArithMean(b) {
    var len = b.length;
    if(len == 0) {
	      return { "$nat" : 0 };
    } else {
	      return { "$nat" : Math.floor(natSum(b)/len) };
    }
}
function floatOfNat(v) {
    return v.$nat;
}

/* Float */
function floatSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i++)
	      result += b[i];
    return result;
}
function floatArithMean(b) {
    var len = b.length;
    if(len == 0) {
	      return 0;
    } else {
	      return floatSum(b)/len;
    }
}

/* Not used */
// from: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions?redirectlocale=en-US&redirectslug=JavaScript%2FGuide%2FRegular_Expressions
function escapeRegExp(string){
    return string.replace(/([.*+?^=!:${}()|\[\]\/\\])/g, "\\$1");
}
function fastdistinct(b) { // Not used
    b1 = b.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    b1.sort(compare);
    var result = [ ];
    var v1 = null;
    var v2 = null;
    for (var i=0; i<b1.length; i++) {
        var v1 = b1[i];
	      if (i == (b1.length -1)) {
	          result.push(v1);
	      }
	      else {
	          v2 = b1[i+1];
	          if (equal(v1,v2)) {
	          } else {
		            result.push(v1);
	          }
	          v1 = v2;
	      }
    }
    return result;
}
