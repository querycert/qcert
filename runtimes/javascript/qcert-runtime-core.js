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
function mustBeArray(obj) {
    if (Array.isArray(obj)) {
        return;
    }
    throw new Error('Expected an array but got: ' + JSON.stringify(obj));
}
function natBox(v) {
    return { '$nat': v };
}
function natUnbox(v) {
    return v.$nat;
}
function mkLeft(v) {
    return { '$left' : v };
}
function mkRight(v) {
    return { '$right' : v };
}
function sub_brand(b1,b2) {
    var bsub=null;
    var bsup=null;
    for (var i=0; i<inheritance.length; i = i+1) {
        bsub = inheritance[i].sub;
        bsup = inheritance[i].sup;
        if ((b1 === bsub) && (b2 === bsup)) return true;
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
    var t1 = typeof v1, t2 = typeof v2;
    if (t1 === 'object' && v1 !== null) {
        if (Object.prototype.hasOwnProperty.call(v1,'$nat')) { t1 = 'number'; v1 = v1.$nat; }
    };
    if (t2 === 'object' && v2 !== null) {
        if (Object.prototype.hasOwnProperty.call(v2,'$nat')) { t2 = 'number'; v2 = v2.$nat; }
    };
    if (t1 != t2)
        return t1 < t2 ? -1 : +1;
    var a1 = {}.toString.apply(v1), a2 = {}.toString.apply(v2);
    if (a1 != a2)
        return a1 < a2 ? -1 : +1;
    if (a1 === '[object Array]') {
        v1 = v1.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
        v2 = v2.slice(); /* So we do the sort/compare on a clone of the original array */
        v1.sort(compare);
        v2.sort(compare);
    }
    if (t1 === 'object') {
        var fields1 = [];
        var fields2 = [];
        for (var f1 in v1) { fields1.push(f1); }
        for (var f2 in v2) { fields2.push(f2); }
        fields1 = fields1.sort(compare);
        fields2 = fields2.sort(compare);
        for (var i = 0; i < fields1.length; i = i+1) {
            if (!(Object.prototype.hasOwnProperty.call(v2,fields1[i])))
                return -1;
            var fc = compare(v1[fields1[i]], v2[fields1[i]]);
            if (fc != 0)
                return fc;
        }
        for (var i = 0; i < fields2.length; i = i+1) {
            if (!(Object.prototype.hasOwnProperty.call(v1,fields2[i])))
                return +1;
        }
        return 0;
    }
    if (v1 != v2)
        return v1 < v2 ? -1 : +1;
    return 0;
}
function toString(v) {
    return toStringQ(v, '');
}
function toText(v) {
    return toStringQ(v, '');
}
function toStringQ(v, quote) {
    if (v === null)
        return 'null';
    var t = typeof v;
    if (t === 'string')
        return quote + v + quote;
    if (t === 'boolean')
        return '' + v;
    if (t === 'number') {
        if (Math.floor(v) === v) return (new Number(v)).toFixed(1); // Make sure there is always decimal point
        else return '' + v;
    }
    if ({}.toString.apply(v) === '[object Array]') {
        v = v.slice();
        v.sort();
        var result = '[';
        for (var i=0, n=v.length; i<n; i = i+1) {
            if (i > 0)
                result += ', ';
            result += toStringQ(v[i], quote);
        }
        return result + ']';
    }
    if(Object.prototype.hasOwnProperty.call(v,'$nat')){
        return '' + v.$nat;
    }
    var result2 = '';
    if (v.$class) { // branded value
        result2 += '<';
        result2 += v.$class;
        result2 += ':';
        result2 += toStringQ(v.$data, quote);
        result2 += '>';
    } else { // record
        // First need to sort
        var sortable = [];
        for (var key in v) {
            sortable.push({ key: key, val: v[key] });
        }
        sortable.sort(function(a, b) { return a.key.localeCompare(b.key); });
        var result2 = '{';
        var first = true;
        for (var i=0, n=sortable.length; i<n; i = i+1) {
            if (first) first = false; else result2 += ', ';
            result2 += toStringQ(sortable[i].key, quote) + '->' + toStringQ(sortable[i].val, quote);
        }
        result2 += '}';
    }
    return result2 + '';
}

/* Record */
function recConcat(r1, r2) {
    var result = { };
    for (var key2 in r2)
        result[key2] = r2[key2];
    for (var key1 in r1)
        if (!(Object.prototype.hasOwnProperty.call(r2,key1)))
            result[key1] = r1[key1];
    return result;
}
function recMerge(r1, r2) {
    var result = { };
    for (var key1 in r1)
        result[key1] = r1[key1];
    for (var key2 in r2) {
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
    var result = { };
    for (var key in r)
        if (key != f)
            result[key] = r[key];
    return result;
}
function recProject(r1, p2) {
    var result = { };
    for (var key1 in r1) {
        if (!(p2.indexOf(key1) === -1))
            result[key1] = r1[key1];
    }
    return result;
}
function recDot(receiver, member) {
    if (typeof receiver === 'object' && Object.prototype.hasOwnProperty.call(receiver,member)) {
        return receiver[member];
    }
    throw new Error('TypeError: recDot called on non-record');
}

/* Sum */
function either(v) {
    if (typeof v === 'object') {
        if (Object.prototype.hasOwnProperty.call(v,'$left')) {
            return true;
        } else if (Object.prototype.hasOwnProperty.call(v,'$right')) {
            return false;
        } else {
            throw new Error('TypeError: either called on non-sum');
        }
    }
    throw new Error('TypeError: either called on non-sum');
}
function toLeft(v) {
    if (typeof v === 'object' && Object.prototype.hasOwnProperty.call(v,'$left')) {
        return v.$left;
    }
    throw new Error('TypeError: toLeft called on non-sum');
}
function toRight(v) {
    if (typeof v === 'object' && Object.prototype.hasOwnProperty.call(v,'$right')) {
        return v.$right;
    }
    throw new Error('TypeError: toRight called on non-sum');
}

/* Brand */
function brand(b,v) {
    return { '$class' : b, '$data' : v };
}
function unbrand(v) {
    if (typeof v === 'object' && Object.prototype.hasOwnProperty.call(v,'$class') && Object.prototype.hasOwnProperty.call(v,'$data')) {
        return v.$data;
    }
    throw new Error('TypeError: unbrand called on non-object');
}
function cast(brands,v) {
    mustBeArray(brands);
    var type = v.$class;
    mustBeArray(type);
    if (brands.length === 1 && brands[0] === 'Any') { /* cast to top of inheritance is built-in */
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
    for (var i=0; i<b.length; i = i+1) {
        var v = b[i];
        var dup = false;
        for (var j=0; j<result.length; j = j+1) {
            if (equal(v,result[j])) { dup = true; break; }
        }
        if (!(dup)) { result.push(v); } else { dup = false; }
    }
    return result;
}
function singleton(v) {
    if (v.length === 1) {
        return mkLeft(v[0]);
    } else {
        return mkRight(null); /* Not a singleton */
    }
}
function flatten(aOuter) {
    var result = [ ];
    for (var iOuter=0, nOuter=aOuter.length; iOuter<nOuter; iOuter = iOuter+1) {
        var aInner = aOuter[iOuter];
        for (var iInner=0, nInner=aInner.length; iInner<nInner; iInner = iInner+1)
            result.push(aInner[iInner]);
    }
    return result;
}
function union(b1, b2) {
    var result = [ ];
    for (var i1=0; i1<b1.length; i1 = i1+1)
        result.push(b1[i1]);
    for (var i2=0; i2<b2.length; i2 = i2+1)
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
    for (var i1=0; i1<v1.length; i1=i1+1) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) i2=i2+1;
        if (i2 < length2) {
            if(compare(v1[i1],v2[i2]) === (-1)) { result.push(v1[i1]); } else { i2=i2+1; }
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
    for (var i1=0; i1<v1.length; i1=i1+1) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) i2=i2+1;
        if (i2 < length2) {
            if(compare(v1[i1],v2[i2]) === 0) result.push(v1[i1]);
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
    for (var i1=0; i1<v1.length; i1=i1+1) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) { result.push(v2[i2]); i2=i2+1; }
        if (i2 < length2) {
            if(compare(v1[i1],v2[i2]) === 0) i2=i2+1;
        }
        result.push(v1[i1]);
    }
    while (i2 < length2) { result.push(v2[i2]); i2=i2+1; }
    return result;
}
function nth(b1, n) {
    var index = n;
    if(Object.prototype.hasOwnProperty.call(n,'$nat')){
        index = n.$nat;
    }
    if (b1[index]) {
        return mkLeft(b1[index]);
    } else {
        return mkRight(null);
    }
}
function count(v) {
    return natBox(v.length);
}
function contains(v, b) {
    for (var i=0; i<b.length; i = i+1)
        if (equal(v, toLeft(b[i])))
            return true;
    return false;
}
function compareOfMultipleCriterias(scl) {
    return function(a,b) {
        var current_compare = 0;
        for (var i=0; i<scl.length; i = i+1) {
            var sc = scl[i];
            if (Object.prototype.hasOwnProperty.call(sc,'asc')) { current_compare = compare(recDot(a,sc['asc']), recDot(b,sc['asc'])); }
            else if (Object.prototype.hasOwnProperty.call(sc,'desc')) { current_compare = -(compare(recDot(a,sc['asc']), recDot(b,sc['asc']))); }

            if (current_compare === -1) { return -1; }
            else if(current_compare === 1) { return 1; }
        }
        return current_compare;
    }
    
}
function sort(b,scl) {
    var result = [ ];
    if (scl.length === 0) { return b; } // Check for no sorting criteria
    var compareFun = compareOfMultipleCriterias(scl);
    result = b.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    result.sort(compareFun);
    return result;
}
function groupBy(l) { // Not implemented
    throw new Error('groupBy not implemented');
}

/* String */
function length(v) {
    return natBox(v.length);
}
function substring(v, start, len) {
    return v.substring(natUnbox(start),natUnbox(len));
}
function substringEnd(v, start) {
    return v.substring(natUnbox(start));
}
function stringJoin(sep, v) {
    return v.join(sep);
}
function like(pat, s) {
    var reg1 = escapeRegExp(pat);
    var reg2 = reg1.replace(/_/g, '.').replace(/%/g, '.*');
    var reg3 = new RegExp(reg2);
    return reg3.test(s);
}

/* Integer */
function natLt(v1, v2) {
    return natUnbox(v1) < natUnbox(v2);
}
function natLe(v1, v2) {
    return natUnbox(v1) <= natUnbox(v2);
}
function natPlus(v1, v2) {
    return natBox(natUnbox(v1) + natUnbox(v2));
}
function natMinus(v1, v2) {
    return natBox(natUnbox(v1) - natUnbox(v2));
}
function natMult(v1, v2) {
    return natBox(natUnbox(v1) * natUnbox(v2));
}
function natDiv(v1, v2) {
    return natBox(Math.floor(natUnbox(v1) / natUnbox(v2)));
}
function natRem(v1, v2) {
    return natBox(Math.floor(natUnbox(v1) % natUnbox(v2)));
}
function natAbs(v) {
    return natBox(Math.abs(natUnbox(v1),natUnbox(v2)));
}
function natLog2(v) {
    return natBox(Math.floor(Math.log2(natUnbox(v)))); // Default Z.log2 is log_inf, biggest integer lower than log2
}
function natSqrt(v) {
    return natBox(Math.floor(Math.sqrt(natUnbox(v)))); // See Z.sqrt biggest integer lower than sqrt
}
function natMinPair(v1, v2) {
    return natBox(Math.min(natUnbox(v1),natUnbox(v2)));
}
function natMaxPair(v1, v2) {
    return natBox(Math.max(natUnbox(v1),natUnbox(v2)));
}
function natSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i = i+1)
        result += natUnbox(b[i]);
    return natBox(result);
}
function natMin(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i = i+1)
        numbers.push(natUnbox(b[i]));
    return natBox(Math.min.apply(Math,numbers));
}
function natMax(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i = i+1)
        numbers.push(natUnbox(b[i]));
    return natBox(Math.max.apply(Math,numbers));
}
function natArithMean(b) {
    var len = b.length;
    if(len === 0) {
        return natBox(0);
    } else {
        return natBox(Math.floor(natSum(b)/len));
    }
}
function floatOfNat(v) {
    return natUnbox(v);
}

/* Float */
function floatSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i = i+1)
        result += b[i];
    return result;
}
function floatArithMean(b) {
    var len = b.length;
    if(len === 0) {
        return 0;
    } else {
        return floatSum(b)/len;
    }
}
function natOfFloat(v) {
    return natBox(Math.trunc(v));
}
