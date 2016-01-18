"use strict";
// This object will hold all exports.
var Haste = {};

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(self, other), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4,_){var _5=B(A1(_3,_)),_6=B(A1(_4,_));return _5;},_7=function(_8,_9,_){var _a=B(A1(_8,_)),_b=B(A1(_9,_));return new T(function(){return B(A1(_a,_b));});},_c=function(_d,_e,_){var _f=B(A1(_e,_));return _d;},_g=function(_h,_i,_){var _j=B(A1(_i,_));return new T(function(){return B(A1(_h,_j));});},_k=new T2(0,_g,_c),_l=function(_m,_){return _m;},_n=function(_o,_p,_){var _q=B(A1(_o,_));return new F(function(){return A1(_p,_);});},_r=new T5(0,_k,_l,_7,_n,_2),_s=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_t=new T(function(){return B(unCStr("base"));}),_u=new T(function(){return B(unCStr("IOException"));}),_v=__Z,_w=new T(function(){var _x=hs_wordToWord64(new Long(4053623282,1685460941,true)),_y=hs_wordToWord64(new Long(3693590983,2507416641,true));return new T5(0,_x,_y,new T5(0,_x,_y,_t,_s,_u),_v,_v);}),_z=function(_A){return E(_w);},_B=function(_C){return E(E(_C).a);},_D=function(_E,_F,_G){var _H=B(A1(_E,_)),_I=B(A1(_F,_)),_J=hs_eqWord64(_H.a,_I.a);if(!_J){return __Z;}else{var _K=hs_eqWord64(_H.b,_I.b);return (!_K)?__Z:new T1(1,_G);}},_L=function(_M){var _N=E(_M);return new F(function(){return _D(B(_B(_N.a)),_z,_N.b);});},_O=new T(function(){return B(unCStr(": "));}),_P=new T(function(){return B(unCStr(")"));}),_Q=new T(function(){return B(unCStr(" ("));}),_R=function(_S,_T){var _U=E(_S);return (_U._==0)?E(_T):new T2(1,_U.a,new T(function(){return B(_R(_U.b,_T));}));},_V=new T(function(){return B(unCStr("interrupted"));}),_W=new T(function(){return B(unCStr("system error"));}),_X=new T(function(){return B(unCStr("unsatisified constraints"));}),_Y=new T(function(){return B(unCStr("user error"));}),_Z=new T(function(){return B(unCStr("permission denied"));}),_10=new T(function(){return B(unCStr("illegal operation"));}),_11=new T(function(){return B(unCStr("end of file"));}),_12=new T(function(){return B(unCStr("resource exhausted"));}),_13=new T(function(){return B(unCStr("resource busy"));}),_14=new T(function(){return B(unCStr("does not exist"));}),_15=new T(function(){return B(unCStr("already exists"));}),_16=new T(function(){return B(unCStr("resource vanished"));}),_17=new T(function(){return B(unCStr("timeout"));}),_18=new T(function(){return B(unCStr("unsupported operation"));}),_19=new T(function(){return B(unCStr("hardware fault"));}),_1a=new T(function(){return B(unCStr("inappropriate type"));}),_1b=new T(function(){return B(unCStr("invalid argument"));}),_1c=new T(function(){return B(unCStr("failed"));}),_1d=new T(function(){return B(unCStr("protocol error"));}),_1e=function(_1f,_1g){switch(E(_1f)){case 0:return new F(function(){return _R(_15,_1g);});break;case 1:return new F(function(){return _R(_14,_1g);});break;case 2:return new F(function(){return _R(_13,_1g);});break;case 3:return new F(function(){return _R(_12,_1g);});break;case 4:return new F(function(){return _R(_11,_1g);});break;case 5:return new F(function(){return _R(_10,_1g);});break;case 6:return new F(function(){return _R(_Z,_1g);});break;case 7:return new F(function(){return _R(_Y,_1g);});break;case 8:return new F(function(){return _R(_X,_1g);});break;case 9:return new F(function(){return _R(_W,_1g);});break;case 10:return new F(function(){return _R(_1d,_1g);});break;case 11:return new F(function(){return _R(_1c,_1g);});break;case 12:return new F(function(){return _R(_1b,_1g);});break;case 13:return new F(function(){return _R(_1a,_1g);});break;case 14:return new F(function(){return _R(_19,_1g);});break;case 15:return new F(function(){return _R(_18,_1g);});break;case 16:return new F(function(){return _R(_17,_1g);});break;case 17:return new F(function(){return _R(_16,_1g);});break;default:return new F(function(){return _R(_V,_1g);});}},_1h=new T(function(){return B(unCStr("}"));}),_1i=new T(function(){return B(unCStr("{handle: "));}),_1j=function(_1k,_1l,_1m,_1n,_1o,_1p){var _1q=new T(function(){var _1r=new T(function(){var _1s=new T(function(){var _1t=E(_1n);if(!_1t._){return E(_1p);}else{var _1u=new T(function(){return B(_R(_1t,new T(function(){return B(_R(_P,_1p));},1)));},1);return B(_R(_Q,_1u));}},1);return B(_1e(_1l,_1s));}),_1v=E(_1m);if(!_1v._){return E(_1r);}else{return B(_R(_1v,new T(function(){return B(_R(_O,_1r));},1)));}}),_1w=E(_1o);if(!_1w._){var _1x=E(_1k);if(!_1x._){return E(_1q);}else{var _1y=E(_1x.a);if(!_1y._){var _1z=new T(function(){var _1A=new T(function(){return B(_R(_1h,new T(function(){return B(_R(_O,_1q));},1)));},1);return B(_R(_1y.a,_1A));},1);return new F(function(){return _R(_1i,_1z);});}else{var _1B=new T(function(){var _1C=new T(function(){return B(_R(_1h,new T(function(){return B(_R(_O,_1q));},1)));},1);return B(_R(_1y.a,_1C));},1);return new F(function(){return _R(_1i,_1B);});}}}else{return new F(function(){return _R(_1w.a,new T(function(){return B(_R(_O,_1q));},1));});}},_1D=function(_1E){var _1F=E(_1E);return new F(function(){return _1j(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_v);});},_1G=function(_1H){return new T2(0,_1I,_1H);},_1J=function(_1K,_1L,_1M){var _1N=E(_1L);return new F(function(){return _1j(_1N.a,_1N.b,_1N.c,_1N.d,_1N.f,_1M);});},_1O=function(_1P,_1Q){var _1R=E(_1P);return new F(function(){return _1j(_1R.a,_1R.b,_1R.c,_1R.d,_1R.f,_1Q);});},_1S=44,_1T=93,_1U=91,_1V=function(_1W,_1X,_1Y){var _1Z=E(_1X);if(!_1Z._){return new F(function(){return unAppCStr("[]",_1Y);});}else{var _20=new T(function(){var _21=new T(function(){var _22=function(_23){var _24=E(_23);if(!_24._){return E(new T2(1,_1T,_1Y));}else{var _25=new T(function(){return B(A2(_1W,_24.a,new T(function(){return B(_22(_24.b));})));});return new T2(1,_1S,_25);}};return B(_22(_1Z.b));});return B(A2(_1W,_1Z.a,_21));});return new T2(1,_1U,_20);}},_26=function(_27,_28){return new F(function(){return _1V(_1O,_27,_28);});},_29=new T3(0,_1J,_1D,_26),_1I=new T(function(){return new T5(0,_z,_29,_1G,_L,_1D);}),_2a=new T(function(){return E(_1I);}),_2b=function(_2c){return E(E(_2c).c);},_2d=__Z,_2e=7,_2f=function(_2g){return new T6(0,_2d,_2e,_v,_2g,_2d,_2d);},_2h=function(_2i,_){var _2j=new T(function(){return B(A2(_2b,_2a,new T(function(){return B(A1(_2f,_2i));})));});return new F(function(){return die(_2j);});},_2k=function(_2l,_){return new F(function(){return _2h(_2l,_);});},_2m=function(_2n){return new F(function(){return A1(_2k,_2n);});},_2o=function(_2p,_2q,_){var _2r=B(A1(_2p,_));return new F(function(){return A2(_2q,_2r,_);});},_2s=new T5(0,_r,_2o,_n,_l,_2m),_2t=function(_2u){return E(_2u);},_2v=new T2(0,_2s,_2t),_2w=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2x=function(_){return new F(function(){return __jsNull();});},_2y=function(_2z){var _2A=B(A1(_2z,_));return E(_2A);},_2B=new T(function(){return B(_2y(_2x));}),_2C=new T(function(){return E(_2B);}),_2D=function(_2E){return E(E(_2E).b);},_2F=function(_2G,_2H){var _2I=function(_){var _2J=__app1(E(_2w),E(_2H)),_2K=__eq(_2J,E(_2C));return (E(_2K)==0)?new T1(1,_2J):_2d;};return new F(function(){return A2(_2D,_2G,_2I);});},_2L=new T(function(){return B(unCStr("Pattern match failure in do expression at barshare.hs:116:3-8"));}),_2M=new T6(0,_2d,_2e,_v,_2L,_2d,_2d),_2N=new T(function(){return B(_1G(_2M));}),_2O="canvas",_2P=new T2(0,_2v,_l),_2Q=0,_2R=function(_){return _2Q;},_2S=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_2T=0,_2U=6.283185307179586,_2V=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_2W=function(_2X,_2Y,_2Z,_30,_){var _31=__app3(E(_2V),_30,_2X+_2Z,_2Y),_32=__apply(E(_2S),new T2(1,_2U,new T2(1,_2T,new T2(1,_2Z,new T2(1,_2Y,new T2(1,_2X,new T2(1,_30,_v)))))));return new F(function(){return _2R(_);});},_33=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_34=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_35=function(_36,_37,_){var _38=__app1(E(_33),_37),_39=B(A2(_36,_37,_)),_3a=__app1(E(_34),_37);return new F(function(){return _2R(_);});},_3b=function(_3c,_3d){var _3e=jsShowI(_3c);return new F(function(){return _R(fromJSStr(_3e),_3d);});},_3f=41,_3g=40,_3h=function(_3i,_3j,_3k){if(_3j>=0){return new F(function(){return _3b(_3j,_3k);});}else{if(_3i<=6){return new F(function(){return _3b(_3j,_3k);});}else{return new T2(1,_3g,new T(function(){var _3l=jsShowI(_3j);return B(_R(fromJSStr(_3l),new T2(1,_3f,_3k)));}));}}},_3m=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_3n=function(_3o,_3p,_3q){var _3r=new T(function(){return toJSStr(E(_3q));});return function(_3s,_){var _3t=__app4(E(_3m),E(_3s),E(_3r),E(_3o),E(_3p));return new F(function(){return _2R(_);});};},_3u=new T(function(){return eval("(function(e){e.width = e.width;})");}),_3v=",",_3w="rgba(",_3x=new T(function(){return toJSStr(_v);}),_3y="rgb(",_3z=")",_3A=new T2(1,_3z,_v),_3B=function(_3C){var _3D=E(_3C);if(!_3D._){var _3E=jsCat(new T2(1,_3y,new T2(1,new T(function(){return String(_3D.a);}),new T2(1,_3v,new T2(1,new T(function(){return String(_3D.b);}),new T2(1,_3v,new T2(1,new T(function(){return String(_3D.c);}),_3A)))))),E(_3x));return E(_3E);}else{var _3F=jsCat(new T2(1,_3w,new T2(1,new T(function(){return String(_3D.a);}),new T2(1,_3v,new T2(1,new T(function(){return String(_3D.b);}),new T2(1,_3v,new T2(1,new T(function(){return String(_3D.c);}),new T2(1,_3v,new T2(1,new T(function(){return String(_3D.d);}),_3A)))))))),E(_3x));return E(_3F);}},_3G="strokeStyle",_3H="fillStyle",_3I=new T(function(){return eval("(function(e,p){return e[p].toString();})");}),_3J=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_3K=function(_3L,_3M){var _3N=new T(function(){return B(_3B(_3L));});return function(_3O,_){var _3P=E(_3O),_3Q=E(_3H),_3R=E(_3I),_3S=__app2(_3R,_3P,_3Q),_3T=E(_3G),_3U=__app2(_3R,_3P,_3T),_3V=E(_3N),_3W=E(_3J),_3X=__app3(_3W,_3P,_3Q,_3V),_3Y=__app3(_3W,_3P,_3T,_3V),_3Z=B(A2(_3M,_3P,_)),_40=String(_3S),_41=__app3(_3W,_3P,_3Q,_40),_42=String(_3U),_43=__app3(_3W,_3P,_3T,_42);return new F(function(){return _2R(_);});};},_44=new T3(0,0,255,0),_45=new T3(0,255,0,0),_46=new T3(0,0,0,0),_47=new T1(0,16),_48=function(_49){var _4a=E(_49),_4b=E(_4a.a);return new T2(0,Math.sqrt(Math.pow( -E(_4b.a),2)+Math.pow( -E(_4b.b),2)),_4a);},_4c=function(_4d,_4e){var _4f=E(E(_4d).a),_4g=E(E(_4e).a);return (_4f>=_4g)?(_4f!=_4g)?2:1:0;},_4h=function(_4i,_){var _4j=__app1(E(_1),_4i);if(!_4j){return _2d;}else{var _4k=__app1(E(_0),_4i);return new T1(1,new T2(0,_4k,_4i));}},_4l=function(_4m,_){return new F(function(){return _4h(E(_4m),_);});},_4n=function(_4o){return E(_4o).b;},_4p=new T2(0,_4n,_4l),_4q=function(_4r){return E(E(_4r).a);},_4s=function(_4t){return E(E(_4t).b);},_4u=function(_4v){return new F(function(){return fromJSStr(E(_4v));});},_4w=function(_4x){return E(E(_4x).a);},_4y=function(_4z,_4A,_4B,_4C){var _4D=new T(function(){var _4E=function(_){var _4F=__app2(E(_3I),B(A2(_4w,_4z,_4B)),E(_4C));return new T(function(){return String(_4F);});};return E(_4E);});return new F(function(){return A2(_2D,_4A,_4D);});},_4G=function(_4H){return E(E(_4H).d);},_4I=function(_4J,_4K,_4L,_4M){var _4N=B(_4q(_4K)),_4O=new T(function(){return B(_4G(_4N));}),_4P=function(_4Q){return new F(function(){return A1(_4O,new T(function(){return B(_4u(_4Q));}));});},_4R=new T(function(){return B(_4y(_4J,_4K,_4L,new T(function(){return toJSStr(E(_4M));},1)));});return new F(function(){return A3(_4s,_4N,_4R,_4P);});},_4S=new T(function(){return B(unCStr("width"));}),_4T=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_4U=new T(function(){return B(err(_4T));}),_4V=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_4W=new T(function(){return B(err(_4V));}),_4X=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4Y=new T(function(){return B(unCStr("base"));}),_4Z=new T(function(){return B(unCStr("PatternMatchFail"));}),_50=new T(function(){var _51=hs_wordToWord64(new Long(18445595,3739165398,true)),_52=hs_wordToWord64(new Long(52003073,3246954884,true));return new T5(0,_51,_52,new T5(0,_51,_52,_4Y,_4X,_4Z),_v,_v);}),_53=function(_54){return E(_50);},_55=function(_56){var _57=E(_56);return new F(function(){return _D(B(_B(_57.a)),_53,_57.b);});},_58=function(_59){return E(E(_59).a);},_5a=function(_5b){return new T2(0,_5c,_5b);},_5d=function(_5e,_5f){return new F(function(){return _R(E(_5e).a,_5f);});},_5g=function(_5h,_5i){return new F(function(){return _1V(_5d,_5h,_5i);});},_5j=function(_5k,_5l,_5m){return new F(function(){return _R(E(_5l).a,_5m);});},_5n=new T3(0,_5j,_58,_5g),_5c=new T(function(){return new T5(0,_53,_5n,_5a,_55,_58);}),_5o=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5p=function(_5q,_5r){return new F(function(){return die(new T(function(){return B(A2(_2b,_5r,_5q));}));});},_5s=function(_5t,_5u){return new F(function(){return _5p(_5t,_5u);});},_5v=function(_5w,_5x){var _5y=E(_5x);if(!_5y._){return new T2(0,_v,_v);}else{var _5z=_5y.a;if(!B(A1(_5w,_5z))){return new T2(0,_v,_5y);}else{var _5A=new T(function(){var _5B=B(_5v(_5w,_5y.b));return new T2(0,_5B.a,_5B.b);});return new T2(0,new T2(1,_5z,new T(function(){return E(E(_5A).a);})),new T(function(){return E(E(_5A).b);}));}}},_5C=32,_5D=new T(function(){return B(unCStr("\n"));}),_5E=function(_5F){return (E(_5F)==124)?false:true;},_5G=function(_5H,_5I){var _5J=B(_5v(_5E,B(unCStr(_5H)))),_5K=_5J.a,_5L=function(_5M,_5N){var _5O=new T(function(){var _5P=new T(function(){return B(_R(_5I,new T(function(){return B(_R(_5N,_5D));},1)));});return B(unAppCStr(": ",_5P));},1);return new F(function(){return _R(_5M,_5O);});},_5Q=E(_5J.b);if(!_5Q._){return new F(function(){return _5L(_5K,_v);});}else{if(E(_5Q.a)==124){return new F(function(){return _5L(_5K,new T2(1,_5C,_5Q.b));});}else{return new F(function(){return _5L(_5K,_v);});}}},_5R=function(_5S){return new F(function(){return _5s(new T1(0,new T(function(){return B(_5G(_5S,_5o));})),_5c);});},_5T=new T(function(){return B(_5R("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_5U=function(_5V,_5W){while(1){var _5X=B((function(_5Y,_5Z){var _60=E(_5Y);switch(_60._){case 0:var _61=E(_5Z);if(!_61._){return __Z;}else{_5V=B(A1(_60.a,_61.a));_5W=_61.b;return __continue;}break;case 1:var _62=B(A1(_60.a,_5Z)),_63=_5Z;_5V=_62;_5W=_63;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_60.a,_5Z),new T(function(){return B(_5U(_60.b,_5Z));}));default:return E(_60.a);}})(_5V,_5W));if(_5X!=__continue){return _5X;}}},_64=function(_65,_66){var _67=function(_68){var _69=E(_66);if(_69._==3){return new T2(3,_69.a,new T(function(){return B(_64(_65,_69.b));}));}else{var _6a=E(_65);if(_6a._==2){return E(_69);}else{var _6b=E(_69);if(_6b._==2){return E(_6a);}else{var _6c=function(_6d){var _6e=E(_6b);if(_6e._==4){var _6f=function(_6g){return new T1(4,new T(function(){return B(_R(B(_5U(_6a,_6g)),_6e.a));}));};return new T1(1,_6f);}else{var _6h=E(_6a);if(_6h._==1){var _6i=_6h.a,_6j=E(_6e);if(!_6j._){return new T1(1,function(_6k){return new F(function(){return _64(B(A1(_6i,_6k)),_6j);});});}else{var _6l=function(_6m){return new F(function(){return _64(B(A1(_6i,_6m)),new T(function(){return B(A1(_6j.a,_6m));}));});};return new T1(1,_6l);}}else{var _6n=E(_6e);if(!_6n._){return E(_5T);}else{var _6o=function(_6p){return new F(function(){return _64(_6h,new T(function(){return B(A1(_6n.a,_6p));}));});};return new T1(1,_6o);}}}},_6q=E(_6a);switch(_6q._){case 1:var _6r=E(_6b);if(_6r._==4){var _6s=function(_6t){return new T1(4,new T(function(){return B(_R(B(_5U(B(A1(_6q.a,_6t)),_6t)),_6r.a));}));};return new T1(1,_6s);}else{return new F(function(){return _6c(_);});}break;case 4:var _6u=_6q.a,_6v=E(_6b);switch(_6v._){case 0:var _6w=function(_6x){var _6y=new T(function(){return B(_R(_6u,new T(function(){return B(_5U(_6v,_6x));},1)));});return new T1(4,_6y);};return new T1(1,_6w);case 1:var _6z=function(_6A){var _6B=new T(function(){return B(_R(_6u,new T(function(){return B(_5U(B(A1(_6v.a,_6A)),_6A));},1)));});return new T1(4,_6B);};return new T1(1,_6z);default:return new T1(4,new T(function(){return B(_R(_6u,_6v.a));}));}break;default:return new F(function(){return _6c(_);});}}}}},_6C=E(_65);switch(_6C._){case 0:var _6D=E(_66);if(!_6D._){var _6E=function(_6F){return new F(function(){return _64(B(A1(_6C.a,_6F)),new T(function(){return B(A1(_6D.a,_6F));}));});};return new T1(0,_6E);}else{return new F(function(){return _67(_);});}break;case 3:return new T2(3,_6C.a,new T(function(){return B(_64(_6C.b,_66));}));default:return new F(function(){return _67(_);});}},_6G=new T(function(){return B(unCStr("("));}),_6H=new T(function(){return B(unCStr(")"));}),_6I=function(_6J,_6K){while(1){var _6L=E(_6J);if(!_6L._){return (E(_6K)._==0)?true:false;}else{var _6M=E(_6K);if(!_6M._){return false;}else{if(E(_6L.a)!=E(_6M.a)){return false;}else{_6J=_6L.b;_6K=_6M.b;continue;}}}}},_6N=function(_6O,_6P){return E(_6O)!=E(_6P);},_6Q=function(_6R,_6S){return E(_6R)==E(_6S);},_6T=new T2(0,_6Q,_6N),_6U=function(_6V,_6W){while(1){var _6X=E(_6V);if(!_6X._){return (E(_6W)._==0)?true:false;}else{var _6Y=E(_6W);if(!_6Y._){return false;}else{if(E(_6X.a)!=E(_6Y.a)){return false;}else{_6V=_6X.b;_6W=_6Y.b;continue;}}}}},_6Z=function(_70,_71){return (!B(_6U(_70,_71)))?true:false;},_72=new T2(0,_6U,_6Z),_73=function(_74,_75){var _76=E(_74);switch(_76._){case 0:return new T1(0,function(_77){return new F(function(){return _73(B(A1(_76.a,_77)),_75);});});case 1:return new T1(1,function(_78){return new F(function(){return _73(B(A1(_76.a,_78)),_75);});});case 2:return new T0(2);case 3:return new F(function(){return _64(B(A1(_75,_76.a)),new T(function(){return B(_73(_76.b,_75));}));});break;default:var _79=function(_7a){var _7b=E(_7a);if(!_7b._){return __Z;}else{var _7c=E(_7b.a);return new F(function(){return _R(B(_5U(B(A1(_75,_7c.a)),_7c.b)),new T(function(){return B(_79(_7b.b));},1));});}},_7d=B(_79(_76.a));return (_7d._==0)?new T0(2):new T1(4,_7d);}},_7e=new T0(2),_7f=function(_7g){return new T2(3,_7g,_7e);},_7h=function(_7i,_7j){var _7k=E(_7i);if(!_7k){return new F(function(){return A1(_7j,_2Q);});}else{var _7l=new T(function(){return B(_7h(_7k-1|0,_7j));});return new T1(0,function(_7m){return E(_7l);});}},_7n=function(_7o,_7p,_7q){var _7r=new T(function(){return B(A1(_7o,_7f));}),_7s=function(_7t,_7u,_7v,_7w){while(1){var _7x=B((function(_7y,_7z,_7A,_7B){var _7C=E(_7y);switch(_7C._){case 0:var _7D=E(_7z);if(!_7D._){return new F(function(){return A1(_7p,_7B);});}else{var _7E=_7A+1|0,_7F=_7B;_7t=B(A1(_7C.a,_7D.a));_7u=_7D.b;_7v=_7E;_7w=_7F;return __continue;}break;case 1:var _7G=B(A1(_7C.a,_7z)),_7H=_7z,_7E=_7A,_7F=_7B;_7t=_7G;_7u=_7H;_7v=_7E;_7w=_7F;return __continue;case 2:return new F(function(){return A1(_7p,_7B);});break;case 3:var _7I=new T(function(){return B(_73(_7C,_7B));});return new F(function(){return _7h(_7A,function(_7J){return E(_7I);});});break;default:return new F(function(){return _73(_7C,_7B);});}})(_7t,_7u,_7v,_7w));if(_7x!=__continue){return _7x;}}};return function(_7K){return new F(function(){return _7s(_7r,_7K,0,_7q);});};},_7L=function(_7M){return new F(function(){return A1(_7M,_v);});},_7N=function(_7O,_7P){var _7Q=function(_7R){var _7S=E(_7R);if(!_7S._){return E(_7L);}else{var _7T=_7S.a;if(!B(A1(_7O,_7T))){return E(_7L);}else{var _7U=new T(function(){return B(_7Q(_7S.b));}),_7V=function(_7W){var _7X=new T(function(){return B(A1(_7U,function(_7Y){return new F(function(){return A1(_7W,new T2(1,_7T,_7Y));});}));});return new T1(0,function(_7Z){return E(_7X);});};return E(_7V);}}};return function(_80){return new F(function(){return A2(_7Q,_80,_7P);});};},_81=new T0(6),_82=new T(function(){return B(unCStr("valDig: Bad base"));}),_83=new T(function(){return B(err(_82));}),_84=function(_85,_86){var _87=function(_88,_89){var _8a=E(_88);if(!_8a._){var _8b=new T(function(){return B(A1(_89,_v));});return function(_8c){return new F(function(){return A1(_8c,_8b);});};}else{var _8d=E(_8a.a),_8e=function(_8f){var _8g=new T(function(){return B(_87(_8a.b,function(_8h){return new F(function(){return A1(_89,new T2(1,_8f,_8h));});}));}),_8i=function(_8j){var _8k=new T(function(){return B(A1(_8g,_8j));});return new T1(0,function(_8l){return E(_8k);});};return E(_8i);};switch(E(_85)){case 8:if(48>_8d){var _8m=new T(function(){return B(A1(_89,_v));});return function(_8n){return new F(function(){return A1(_8n,_8m);});};}else{if(_8d>55){var _8o=new T(function(){return B(A1(_89,_v));});return function(_8p){return new F(function(){return A1(_8p,_8o);});};}else{return new F(function(){return _8e(_8d-48|0);});}}break;case 10:if(48>_8d){var _8q=new T(function(){return B(A1(_89,_v));});return function(_8r){return new F(function(){return A1(_8r,_8q);});};}else{if(_8d>57){var _8s=new T(function(){return B(A1(_89,_v));});return function(_8t){return new F(function(){return A1(_8t,_8s);});};}else{return new F(function(){return _8e(_8d-48|0);});}}break;case 16:if(48>_8d){if(97>_8d){if(65>_8d){var _8u=new T(function(){return B(A1(_89,_v));});return function(_8v){return new F(function(){return A1(_8v,_8u);});};}else{if(_8d>70){var _8w=new T(function(){return B(A1(_89,_v));});return function(_8x){return new F(function(){return A1(_8x,_8w);});};}else{return new F(function(){return _8e((_8d-65|0)+10|0);});}}}else{if(_8d>102){if(65>_8d){var _8y=new T(function(){return B(A1(_89,_v));});return function(_8z){return new F(function(){return A1(_8z,_8y);});};}else{if(_8d>70){var _8A=new T(function(){return B(A1(_89,_v));});return function(_8B){return new F(function(){return A1(_8B,_8A);});};}else{return new F(function(){return _8e((_8d-65|0)+10|0);});}}}else{return new F(function(){return _8e((_8d-97|0)+10|0);});}}}else{if(_8d>57){if(97>_8d){if(65>_8d){var _8C=new T(function(){return B(A1(_89,_v));});return function(_8D){return new F(function(){return A1(_8D,_8C);});};}else{if(_8d>70){var _8E=new T(function(){return B(A1(_89,_v));});return function(_8F){return new F(function(){return A1(_8F,_8E);});};}else{return new F(function(){return _8e((_8d-65|0)+10|0);});}}}else{if(_8d>102){if(65>_8d){var _8G=new T(function(){return B(A1(_89,_v));});return function(_8H){return new F(function(){return A1(_8H,_8G);});};}else{if(_8d>70){var _8I=new T(function(){return B(A1(_89,_v));});return function(_8J){return new F(function(){return A1(_8J,_8I);});};}else{return new F(function(){return _8e((_8d-65|0)+10|0);});}}}else{return new F(function(){return _8e((_8d-97|0)+10|0);});}}}else{return new F(function(){return _8e(_8d-48|0);});}}break;default:return E(_83);}}},_8K=function(_8L){var _8M=E(_8L);if(!_8M._){return new T0(2);}else{return new F(function(){return A1(_86,_8M);});}};return function(_8N){return new F(function(){return A3(_87,_8N,_2t,_8K);});};},_8O=16,_8P=8,_8Q=function(_8R){var _8S=function(_8T){return new F(function(){return A1(_8R,new T1(5,new T2(0,_8P,_8T)));});},_8U=function(_8V){return new F(function(){return A1(_8R,new T1(5,new T2(0,_8O,_8V)));});},_8W=function(_8X){switch(E(_8X)){case 79:return new T1(1,B(_84(_8P,_8S)));case 88:return new T1(1,B(_84(_8O,_8U)));case 111:return new T1(1,B(_84(_8P,_8S)));case 120:return new T1(1,B(_84(_8O,_8U)));default:return new T0(2);}};return function(_8Y){return (E(_8Y)==48)?E(new T1(0,_8W)):new T0(2);};},_8Z=function(_90){return new T1(0,B(_8Q(_90)));},_91=function(_92){return new F(function(){return A1(_92,_2d);});},_93=function(_94){return new F(function(){return A1(_94,_2d);});},_95=10,_96=new T1(0,1),_97=new T1(0,2147483647),_98=function(_99,_9a){while(1){var _9b=E(_99);if(!_9b._){var _9c=_9b.a,_9d=E(_9a);if(!_9d._){var _9e=_9d.a,_9f=addC(_9c,_9e);if(!E(_9f.b)){return new T1(0,_9f.a);}else{_99=new T1(1,I_fromInt(_9c));_9a=new T1(1,I_fromInt(_9e));continue;}}else{_99=new T1(1,I_fromInt(_9c));_9a=_9d;continue;}}else{var _9g=E(_9a);if(!_9g._){_99=_9b;_9a=new T1(1,I_fromInt(_9g.a));continue;}else{return new T1(1,I_add(_9b.a,_9g.a));}}}},_9h=new T(function(){return B(_98(_97,_96));}),_9i=function(_9j){var _9k=E(_9j);if(!_9k._){var _9l=E(_9k.a);return (_9l==(-2147483648))?E(_9h):new T1(0, -_9l);}else{return new T1(1,I_negate(_9k.a));}},_9m=new T1(0,10),_9n=function(_9o,_9p){while(1){var _9q=E(_9o);if(!_9q._){return E(_9p);}else{var _9r=_9p+1|0;_9o=_9q.b;_9p=_9r;continue;}}},_9s=function(_9t,_9u){var _9v=E(_9u);return (_9v._==0)?__Z:new T2(1,new T(function(){return B(A1(_9t,_9v.a));}),new T(function(){return B(_9s(_9t,_9v.b));}));},_9w=function(_9x){return new T1(0,_9x);},_9y=function(_9z){return new F(function(){return _9w(E(_9z));});},_9A=new T(function(){return B(unCStr("this should not happen"));}),_9B=new T(function(){return B(err(_9A));}),_9C=function(_9D,_9E){while(1){var _9F=E(_9D);if(!_9F._){var _9G=_9F.a,_9H=E(_9E);if(!_9H._){var _9I=_9H.a;if(!(imul(_9G,_9I)|0)){return new T1(0,imul(_9G,_9I)|0);}else{_9D=new T1(1,I_fromInt(_9G));_9E=new T1(1,I_fromInt(_9I));continue;}}else{_9D=new T1(1,I_fromInt(_9G));_9E=_9H;continue;}}else{var _9J=E(_9E);if(!_9J._){_9D=_9F;_9E=new T1(1,I_fromInt(_9J.a));continue;}else{return new T1(1,I_mul(_9F.a,_9J.a));}}}},_9K=function(_9L,_9M){var _9N=E(_9M);if(!_9N._){return __Z;}else{var _9O=E(_9N.b);return (_9O._==0)?E(_9B):new T2(1,B(_98(B(_9C(_9N.a,_9L)),_9O.a)),new T(function(){return B(_9K(_9L,_9O.b));}));}},_9P=new T1(0,0),_9Q=function(_9R,_9S,_9T){while(1){var _9U=B((function(_9V,_9W,_9X){var _9Y=E(_9X);if(!_9Y._){return E(_9P);}else{if(!E(_9Y.b)._){return E(_9Y.a);}else{var _9Z=E(_9W);if(_9Z<=40){var _a0=function(_a1,_a2){while(1){var _a3=E(_a2);if(!_a3._){return E(_a1);}else{var _a4=B(_98(B(_9C(_a1,_9V)),_a3.a));_a1=_a4;_a2=_a3.b;continue;}}};return new F(function(){return _a0(_9P,_9Y);});}else{var _a5=B(_9C(_9V,_9V));if(!(_9Z%2)){var _a6=B(_9K(_9V,_9Y));_9R=_a5;_9S=quot(_9Z+1|0,2);_9T=_a6;return __continue;}else{var _a6=B(_9K(_9V,new T2(1,_9P,_9Y)));_9R=_a5;_9S=quot(_9Z+1|0,2);_9T=_a6;return __continue;}}}}})(_9R,_9S,_9T));if(_9U!=__continue){return _9U;}}},_a7=function(_a8,_a9){return new F(function(){return _9Q(_a8,new T(function(){return B(_9n(_a9,0));},1),B(_9s(_9y,_a9)));});},_aa=function(_ab){var _ac=new T(function(){var _ad=new T(function(){var _ae=function(_af){return new F(function(){return A1(_ab,new T1(1,new T(function(){return B(_a7(_9m,_af));})));});};return new T1(1,B(_84(_95,_ae)));}),_ag=function(_ah){if(E(_ah)==43){var _ai=function(_aj){return new F(function(){return A1(_ab,new T1(1,new T(function(){return B(_a7(_9m,_aj));})));});};return new T1(1,B(_84(_95,_ai)));}else{return new T0(2);}},_ak=function(_al){if(E(_al)==45){var _am=function(_an){return new F(function(){return A1(_ab,new T1(1,new T(function(){return B(_9i(B(_a7(_9m,_an))));})));});};return new T1(1,B(_84(_95,_am)));}else{return new T0(2);}};return B(_64(B(_64(new T1(0,_ak),new T1(0,_ag))),_ad));});return new F(function(){return _64(new T1(0,function(_ao){return (E(_ao)==101)?E(_ac):new T0(2);}),new T1(0,function(_ap){return (E(_ap)==69)?E(_ac):new T0(2);}));});},_aq=function(_ar){var _as=function(_at){return new F(function(){return A1(_ar,new T1(1,_at));});};return function(_au){return (E(_au)==46)?new T1(1,B(_84(_95,_as))):new T0(2);};},_av=function(_aw){return new T1(0,B(_aq(_aw)));},_ax=function(_ay){var _az=function(_aA){var _aB=function(_aC){return new T1(1,B(_7n(_aa,_91,function(_aD){return new F(function(){return A1(_ay,new T1(5,new T3(1,_aA,_aC,_aD)));});})));};return new T1(1,B(_7n(_av,_93,_aB)));};return new F(function(){return _84(_95,_az);});},_aE=function(_aF){return new T1(1,B(_ax(_aF)));},_aG=function(_aH){return E(E(_aH).a);},_aI=function(_aJ,_aK,_aL){while(1){var _aM=E(_aL);if(!_aM._){return false;}else{if(!B(A3(_aG,_aJ,_aK,_aM.a))){_aL=_aM.b;continue;}else{return true;}}}},_aN=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_aO=function(_aP){return new F(function(){return _aI(_6T,_aP,_aN);});},_aQ=false,_aR=true,_aS=function(_aT){var _aU=new T(function(){return B(A1(_aT,_8P));}),_aV=new T(function(){return B(A1(_aT,_8O));});return function(_aW){switch(E(_aW)){case 79:return E(_aU);case 88:return E(_aV);case 111:return E(_aU);case 120:return E(_aV);default:return new T0(2);}};},_aX=function(_aY){return new T1(0,B(_aS(_aY)));},_aZ=function(_b0){return new F(function(){return A1(_b0,_95);});},_b1=function(_b2){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_3h(9,_b2,_v));}))));});},_b3=function(_b4){var _b5=E(_b4);if(!_b5._){return E(_b5.a);}else{return new F(function(){return I_toInt(_b5.a);});}},_b6=function(_b7,_b8){var _b9=E(_b7);if(!_b9._){var _ba=_b9.a,_bb=E(_b8);return (_bb._==0)?_ba<=_bb.a:I_compareInt(_bb.a,_ba)>=0;}else{var _bc=_b9.a,_bd=E(_b8);return (_bd._==0)?I_compareInt(_bc,_bd.a)<=0:I_compare(_bc,_bd.a)<=0;}},_be=function(_bf){return new T0(2);},_bg=function(_bh){var _bi=E(_bh);if(!_bi._){return E(_be);}else{var _bj=_bi.a,_bk=E(_bi.b);if(!_bk._){return E(_bj);}else{var _bl=new T(function(){return B(_bg(_bk));}),_bm=function(_bn){return new F(function(){return _64(B(A1(_bj,_bn)),new T(function(){return B(A1(_bl,_bn));}));});};return E(_bm);}}},_bo=function(_bp,_bq){var _br=function(_bs,_bt,_bu){var _bv=E(_bs);if(!_bv._){return new F(function(){return A1(_bu,_bp);});}else{var _bw=E(_bt);if(!_bw._){return new T0(2);}else{if(E(_bv.a)!=E(_bw.a)){return new T0(2);}else{var _bx=new T(function(){return B(_br(_bv.b,_bw.b,_bu));});return new T1(0,function(_by){return E(_bx);});}}}};return function(_bz){return new F(function(){return _br(_bp,_bz,_bq);});};},_bA=new T(function(){return B(unCStr("SO"));}),_bB=14,_bC=function(_bD){var _bE=new T(function(){return B(A1(_bD,_bB));});return new T1(1,B(_bo(_bA,function(_bF){return E(_bE);})));},_bG=new T(function(){return B(unCStr("SOH"));}),_bH=1,_bI=function(_bJ){var _bK=new T(function(){return B(A1(_bJ,_bH));});return new T1(1,B(_bo(_bG,function(_bL){return E(_bK);})));},_bM=function(_bN){return new T1(1,B(_7n(_bI,_bC,_bN)));},_bO=new T(function(){return B(unCStr("NUL"));}),_bP=0,_bQ=function(_bR){var _bS=new T(function(){return B(A1(_bR,_bP));});return new T1(1,B(_bo(_bO,function(_bT){return E(_bS);})));},_bU=new T(function(){return B(unCStr("STX"));}),_bV=2,_bW=function(_bX){var _bY=new T(function(){return B(A1(_bX,_bV));});return new T1(1,B(_bo(_bU,function(_bZ){return E(_bY);})));},_c0=new T(function(){return B(unCStr("ETX"));}),_c1=3,_c2=function(_c3){var _c4=new T(function(){return B(A1(_c3,_c1));});return new T1(1,B(_bo(_c0,function(_c5){return E(_c4);})));},_c6=new T(function(){return B(unCStr("EOT"));}),_c7=4,_c8=function(_c9){var _ca=new T(function(){return B(A1(_c9,_c7));});return new T1(1,B(_bo(_c6,function(_cb){return E(_ca);})));},_cc=new T(function(){return B(unCStr("ENQ"));}),_cd=5,_ce=function(_cf){var _cg=new T(function(){return B(A1(_cf,_cd));});return new T1(1,B(_bo(_cc,function(_ch){return E(_cg);})));},_ci=new T(function(){return B(unCStr("ACK"));}),_cj=6,_ck=function(_cl){var _cm=new T(function(){return B(A1(_cl,_cj));});return new T1(1,B(_bo(_ci,function(_cn){return E(_cm);})));},_co=new T(function(){return B(unCStr("BEL"));}),_cp=7,_cq=function(_cr){var _cs=new T(function(){return B(A1(_cr,_cp));});return new T1(1,B(_bo(_co,function(_ct){return E(_cs);})));},_cu=new T(function(){return B(unCStr("BS"));}),_cv=8,_cw=function(_cx){var _cy=new T(function(){return B(A1(_cx,_cv));});return new T1(1,B(_bo(_cu,function(_cz){return E(_cy);})));},_cA=new T(function(){return B(unCStr("HT"));}),_cB=9,_cC=function(_cD){var _cE=new T(function(){return B(A1(_cD,_cB));});return new T1(1,B(_bo(_cA,function(_cF){return E(_cE);})));},_cG=new T(function(){return B(unCStr("LF"));}),_cH=10,_cI=function(_cJ){var _cK=new T(function(){return B(A1(_cJ,_cH));});return new T1(1,B(_bo(_cG,function(_cL){return E(_cK);})));},_cM=new T(function(){return B(unCStr("VT"));}),_cN=11,_cO=function(_cP){var _cQ=new T(function(){return B(A1(_cP,_cN));});return new T1(1,B(_bo(_cM,function(_cR){return E(_cQ);})));},_cS=new T(function(){return B(unCStr("FF"));}),_cT=12,_cU=function(_cV){var _cW=new T(function(){return B(A1(_cV,_cT));});return new T1(1,B(_bo(_cS,function(_cX){return E(_cW);})));},_cY=new T(function(){return B(unCStr("CR"));}),_cZ=13,_d0=function(_d1){var _d2=new T(function(){return B(A1(_d1,_cZ));});return new T1(1,B(_bo(_cY,function(_d3){return E(_d2);})));},_d4=new T(function(){return B(unCStr("SI"));}),_d5=15,_d6=function(_d7){var _d8=new T(function(){return B(A1(_d7,_d5));});return new T1(1,B(_bo(_d4,function(_d9){return E(_d8);})));},_da=new T(function(){return B(unCStr("DLE"));}),_db=16,_dc=function(_dd){var _de=new T(function(){return B(A1(_dd,_db));});return new T1(1,B(_bo(_da,function(_df){return E(_de);})));},_dg=new T(function(){return B(unCStr("DC1"));}),_dh=17,_di=function(_dj){var _dk=new T(function(){return B(A1(_dj,_dh));});return new T1(1,B(_bo(_dg,function(_dl){return E(_dk);})));},_dm=new T(function(){return B(unCStr("DC2"));}),_dn=18,_do=function(_dp){var _dq=new T(function(){return B(A1(_dp,_dn));});return new T1(1,B(_bo(_dm,function(_dr){return E(_dq);})));},_ds=new T(function(){return B(unCStr("DC3"));}),_dt=19,_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,_dt));});return new T1(1,B(_bo(_ds,function(_dx){return E(_dw);})));},_dy=new T(function(){return B(unCStr("DC4"));}),_dz=20,_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,_dz));});return new T1(1,B(_bo(_dy,function(_dD){return E(_dC);})));},_dE=new T(function(){return B(unCStr("NAK"));}),_dF=21,_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,_dF));});return new T1(1,B(_bo(_dE,function(_dJ){return E(_dI);})));},_dK=new T(function(){return B(unCStr("SYN"));}),_dL=22,_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,_dL));});return new T1(1,B(_bo(_dK,function(_dP){return E(_dO);})));},_dQ=new T(function(){return B(unCStr("ETB"));}),_dR=23,_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,_dR));});return new T1(1,B(_bo(_dQ,function(_dV){return E(_dU);})));},_dW=new T(function(){return B(unCStr("CAN"));}),_dX=24,_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,_dX));});return new T1(1,B(_bo(_dW,function(_e1){return E(_e0);})));},_e2=new T(function(){return B(unCStr("EM"));}),_e3=25,_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,_e3));});return new T1(1,B(_bo(_e2,function(_e7){return E(_e6);})));},_e8=new T(function(){return B(unCStr("SUB"));}),_e9=26,_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,_e9));});return new T1(1,B(_bo(_e8,function(_ed){return E(_ec);})));},_ee=new T(function(){return B(unCStr("ESC"));}),_ef=27,_eg=function(_eh){var _ei=new T(function(){return B(A1(_eh,_ef));});return new T1(1,B(_bo(_ee,function(_ej){return E(_ei);})));},_ek=new T(function(){return B(unCStr("FS"));}),_el=28,_em=function(_en){var _eo=new T(function(){return B(A1(_en,_el));});return new T1(1,B(_bo(_ek,function(_ep){return E(_eo);})));},_eq=new T(function(){return B(unCStr("GS"));}),_er=29,_es=function(_et){var _eu=new T(function(){return B(A1(_et,_er));});return new T1(1,B(_bo(_eq,function(_ev){return E(_eu);})));},_ew=new T(function(){return B(unCStr("RS"));}),_ex=30,_ey=function(_ez){var _eA=new T(function(){return B(A1(_ez,_ex));});return new T1(1,B(_bo(_ew,function(_eB){return E(_eA);})));},_eC=new T(function(){return B(unCStr("US"));}),_eD=31,_eE=function(_eF){var _eG=new T(function(){return B(A1(_eF,_eD));});return new T1(1,B(_bo(_eC,function(_eH){return E(_eG);})));},_eI=new T(function(){return B(unCStr("SP"));}),_eJ=32,_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,_eJ));});return new T1(1,B(_bo(_eI,function(_eN){return E(_eM);})));},_eO=new T(function(){return B(unCStr("DEL"));}),_eP=127,_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,_eP));});return new T1(1,B(_bo(_eO,function(_eT){return E(_eS);})));},_eU=new T2(1,_eQ,_v),_eV=new T2(1,_eK,_eU),_eW=new T2(1,_eE,_eV),_eX=new T2(1,_ey,_eW),_eY=new T2(1,_es,_eX),_eZ=new T2(1,_em,_eY),_f0=new T2(1,_eg,_eZ),_f1=new T2(1,_ea,_f0),_f2=new T2(1,_e4,_f1),_f3=new T2(1,_dY,_f2),_f4=new T2(1,_dS,_f3),_f5=new T2(1,_dM,_f4),_f6=new T2(1,_dG,_f5),_f7=new T2(1,_dA,_f6),_f8=new T2(1,_du,_f7),_f9=new T2(1,_do,_f8),_fa=new T2(1,_di,_f9),_fb=new T2(1,_dc,_fa),_fc=new T2(1,_d6,_fb),_fd=new T2(1,_d0,_fc),_fe=new T2(1,_cU,_fd),_ff=new T2(1,_cO,_fe),_fg=new T2(1,_cI,_ff),_fh=new T2(1,_cC,_fg),_fi=new T2(1,_cw,_fh),_fj=new T2(1,_cq,_fi),_fk=new T2(1,_ck,_fj),_fl=new T2(1,_ce,_fk),_fm=new T2(1,_c8,_fl),_fn=new T2(1,_c2,_fm),_fo=new T2(1,_bW,_fn),_fp=new T2(1,_bQ,_fo),_fq=new T2(1,_bM,_fp),_fr=new T(function(){return B(_bg(_fq));}),_fs=34,_ft=new T1(0,1114111),_fu=92,_fv=39,_fw=function(_fx){var _fy=new T(function(){return B(A1(_fx,_cp));}),_fz=new T(function(){return B(A1(_fx,_cv));}),_fA=new T(function(){return B(A1(_fx,_cB));}),_fB=new T(function(){return B(A1(_fx,_cH));}),_fC=new T(function(){return B(A1(_fx,_cN));}),_fD=new T(function(){return B(A1(_fx,_cT));}),_fE=new T(function(){return B(A1(_fx,_cZ));}),_fF=new T(function(){return B(A1(_fx,_fu));}),_fG=new T(function(){return B(A1(_fx,_fv));}),_fH=new T(function(){return B(A1(_fx,_fs));}),_fI=new T(function(){var _fJ=function(_fK){var _fL=new T(function(){return B(_9w(E(_fK)));}),_fM=function(_fN){var _fO=B(_a7(_fL,_fN));if(!B(_b6(_fO,_ft))){return new T0(2);}else{return new F(function(){return A1(_fx,new T(function(){var _fP=B(_b3(_fO));if(_fP>>>0>1114111){return B(_b1(_fP));}else{return _fP;}}));});}};return new T1(1,B(_84(_fK,_fM)));},_fQ=new T(function(){var _fR=new T(function(){return B(A1(_fx,_eD));}),_fS=new T(function(){return B(A1(_fx,_ex));}),_fT=new T(function(){return B(A1(_fx,_er));}),_fU=new T(function(){return B(A1(_fx,_el));}),_fV=new T(function(){return B(A1(_fx,_ef));}),_fW=new T(function(){return B(A1(_fx,_e9));}),_fX=new T(function(){return B(A1(_fx,_e3));}),_fY=new T(function(){return B(A1(_fx,_dX));}),_fZ=new T(function(){return B(A1(_fx,_dR));}),_g0=new T(function(){return B(A1(_fx,_dL));}),_g1=new T(function(){return B(A1(_fx,_dF));}),_g2=new T(function(){return B(A1(_fx,_dz));}),_g3=new T(function(){return B(A1(_fx,_dt));}),_g4=new T(function(){return B(A1(_fx,_dn));}),_g5=new T(function(){return B(A1(_fx,_dh));}),_g6=new T(function(){return B(A1(_fx,_db));}),_g7=new T(function(){return B(A1(_fx,_d5));}),_g8=new T(function(){return B(A1(_fx,_bB));}),_g9=new T(function(){return B(A1(_fx,_cj));}),_ga=new T(function(){return B(A1(_fx,_cd));}),_gb=new T(function(){return B(A1(_fx,_c7));}),_gc=new T(function(){return B(A1(_fx,_c1));}),_gd=new T(function(){return B(A1(_fx,_bV));}),_ge=new T(function(){return B(A1(_fx,_bH));}),_gf=new T(function(){return B(A1(_fx,_bP));}),_gg=function(_gh){switch(E(_gh)){case 64:return E(_gf);case 65:return E(_ge);case 66:return E(_gd);case 67:return E(_gc);case 68:return E(_gb);case 69:return E(_ga);case 70:return E(_g9);case 71:return E(_fy);case 72:return E(_fz);case 73:return E(_fA);case 74:return E(_fB);case 75:return E(_fC);case 76:return E(_fD);case 77:return E(_fE);case 78:return E(_g8);case 79:return E(_g7);case 80:return E(_g6);case 81:return E(_g5);case 82:return E(_g4);case 83:return E(_g3);case 84:return E(_g2);case 85:return E(_g1);case 86:return E(_g0);case 87:return E(_fZ);case 88:return E(_fY);case 89:return E(_fX);case 90:return E(_fW);case 91:return E(_fV);case 92:return E(_fU);case 93:return E(_fT);case 94:return E(_fS);case 95:return E(_fR);default:return new T0(2);}};return B(_64(new T1(0,function(_gi){return (E(_gi)==94)?E(new T1(0,_gg)):new T0(2);}),new T(function(){return B(A1(_fr,_fx));})));});return B(_64(new T1(1,B(_7n(_aX,_aZ,_fJ))),_fQ));});return new F(function(){return _64(new T1(0,function(_gj){switch(E(_gj)){case 34:return E(_fH);case 39:return E(_fG);case 92:return E(_fF);case 97:return E(_fy);case 98:return E(_fz);case 102:return E(_fD);case 110:return E(_fB);case 114:return E(_fE);case 116:return E(_fA);case 118:return E(_fC);default:return new T0(2);}}),_fI);});},_gk=function(_gl){return new F(function(){return A1(_gl,_2Q);});},_gm=function(_gn){var _go=E(_gn);if(!_go._){return E(_gk);}else{var _gp=E(_go.a),_gq=_gp>>>0,_gr=new T(function(){return B(_gm(_go.b));});if(_gq>887){var _gs=u_iswspace(_gp);if(!E(_gs)){return E(_gk);}else{var _gt=function(_gu){var _gv=new T(function(){return B(A1(_gr,_gu));});return new T1(0,function(_gw){return E(_gv);});};return E(_gt);}}else{var _gx=E(_gq);if(_gx==32){var _gy=function(_gz){var _gA=new T(function(){return B(A1(_gr,_gz));});return new T1(0,function(_gB){return E(_gA);});};return E(_gy);}else{if(_gx-9>>>0>4){if(E(_gx)==160){var _gC=function(_gD){var _gE=new T(function(){return B(A1(_gr,_gD));});return new T1(0,function(_gF){return E(_gE);});};return E(_gC);}else{return E(_gk);}}else{var _gG=function(_gH){var _gI=new T(function(){return B(A1(_gr,_gH));});return new T1(0,function(_gJ){return E(_gI);});};return E(_gG);}}}}},_gK=function(_gL){var _gM=new T(function(){return B(_gK(_gL));}),_gN=function(_gO){return (E(_gO)==92)?E(_gM):new T0(2);},_gP=function(_gQ){return E(new T1(0,_gN));},_gR=new T1(1,function(_gS){return new F(function(){return A2(_gm,_gS,_gP);});}),_gT=new T(function(){return B(_fw(function(_gU){return new F(function(){return A1(_gL,new T2(0,_gU,_aR));});}));}),_gV=function(_gW){var _gX=E(_gW);if(_gX==38){return E(_gM);}else{var _gY=_gX>>>0;if(_gY>887){var _gZ=u_iswspace(_gX);return (E(_gZ)==0)?new T0(2):E(_gR);}else{var _h0=E(_gY);return (_h0==32)?E(_gR):(_h0-9>>>0>4)?(E(_h0)==160)?E(_gR):new T0(2):E(_gR);}}};return new F(function(){return _64(new T1(0,function(_h1){return (E(_h1)==92)?E(new T1(0,_gV)):new T0(2);}),new T1(0,function(_h2){var _h3=E(_h2);if(E(_h3)==92){return E(_gT);}else{return new F(function(){return A1(_gL,new T2(0,_h3,_aQ));});}}));});},_h4=function(_h5,_h6){var _h7=new T(function(){return B(A1(_h6,new T1(1,new T(function(){return B(A1(_h5,_v));}))));}),_h8=function(_h9){var _ha=E(_h9),_hb=E(_ha.a);if(E(_hb)==34){if(!E(_ha.b)){return E(_h7);}else{return new F(function(){return _h4(function(_hc){return new F(function(){return A1(_h5,new T2(1,_hb,_hc));});},_h6);});}}else{return new F(function(){return _h4(function(_hd){return new F(function(){return A1(_h5,new T2(1,_hb,_hd));});},_h6);});}};return new F(function(){return _gK(_h8);});},_he=new T(function(){return B(unCStr("_\'"));}),_hf=function(_hg){var _hh=u_iswalnum(_hg);if(!E(_hh)){return new F(function(){return _aI(_6T,_hg,_he);});}else{return true;}},_hi=function(_hj){return new F(function(){return _hf(E(_hj));});},_hk=new T(function(){return B(unCStr(",;()[]{}`"));}),_hl=new T(function(){return B(unCStr("=>"));}),_hm=new T2(1,_hl,_v),_hn=new T(function(){return B(unCStr("~"));}),_ho=new T2(1,_hn,_hm),_hp=new T(function(){return B(unCStr("@"));}),_hq=new T2(1,_hp,_ho),_hr=new T(function(){return B(unCStr("->"));}),_hs=new T2(1,_hr,_hq),_ht=new T(function(){return B(unCStr("<-"));}),_hu=new T2(1,_ht,_hs),_hv=new T(function(){return B(unCStr("|"));}),_hw=new T2(1,_hv,_hu),_hx=new T(function(){return B(unCStr("\\"));}),_hy=new T2(1,_hx,_hw),_hz=new T(function(){return B(unCStr("="));}),_hA=new T2(1,_hz,_hy),_hB=new T(function(){return B(unCStr("::"));}),_hC=new T2(1,_hB,_hA),_hD=new T(function(){return B(unCStr(".."));}),_hE=new T2(1,_hD,_hC),_hF=function(_hG){var _hH=new T(function(){return B(A1(_hG,_81));}),_hI=new T(function(){var _hJ=new T(function(){var _hK=function(_hL){var _hM=new T(function(){return B(A1(_hG,new T1(0,_hL)));});return new T1(0,function(_hN){return (E(_hN)==39)?E(_hM):new T0(2);});};return B(_fw(_hK));}),_hO=function(_hP){var _hQ=E(_hP);switch(E(_hQ)){case 39:return new T0(2);case 92:return E(_hJ);default:var _hR=new T(function(){return B(A1(_hG,new T1(0,_hQ)));});return new T1(0,function(_hS){return (E(_hS)==39)?E(_hR):new T0(2);});}},_hT=new T(function(){var _hU=new T(function(){return B(_h4(_2t,_hG));}),_hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=function(_hZ){var _i0=E(_hZ),_i1=u_iswalpha(_i0);return (E(_i1)==0)?(E(_i0)==95)?new T1(1,B(_7N(_hi,function(_i2){return new F(function(){return A1(_hG,new T1(3,new T2(1,_i0,_i2)));});}))):new T0(2):new T1(1,B(_7N(_hi,function(_i3){return new F(function(){return A1(_hG,new T1(3,new T2(1,_i0,_i3)));});})));};return B(_64(new T1(0,_hY),new T(function(){return new T1(1,B(_7n(_8Z,_aE,_hG)));})));}),_i4=function(_i5){return (!B(_aI(_6T,_i5,_aN)))?new T0(2):new T1(1,B(_7N(_aO,function(_i6){var _i7=new T2(1,_i5,_i6);if(!B(_aI(_72,_i7,_hE))){return new F(function(){return A1(_hG,new T1(4,_i7));});}else{return new F(function(){return A1(_hG,new T1(2,_i7));});}})));};return B(_64(new T1(0,_i4),_hX));});return B(_64(new T1(0,function(_i8){if(!B(_aI(_6T,_i8,_hk))){return new T0(2);}else{return new F(function(){return A1(_hG,new T1(2,new T2(1,_i8,_v)));});}}),_hW));});return B(_64(new T1(0,function(_i9){return (E(_i9)==34)?E(_hU):new T0(2);}),_hV));});return B(_64(new T1(0,function(_ia){return (E(_ia)==39)?E(new T1(0,_hO)):new T0(2);}),_hT));});return new F(function(){return _64(new T1(1,function(_ib){return (E(_ib)._==0)?E(_hH):new T0(2);}),_hI);});},_ic=0,_id=function(_ie,_if){var _ig=new T(function(){var _ih=new T(function(){var _ii=function(_ij){var _ik=new T(function(){var _il=new T(function(){return B(A1(_if,_ij));});return B(_hF(function(_im){var _in=E(_im);return (_in._==2)?(!B(_6I(_in.a,_6H)))?new T0(2):E(_il):new T0(2);}));}),_io=function(_ip){return E(_ik);};return new T1(1,function(_iq){return new F(function(){return A2(_gm,_iq,_io);});});};return B(A2(_ie,_ic,_ii));});return B(_hF(function(_ir){var _is=E(_ir);return (_is._==2)?(!B(_6I(_is.a,_6G)))?new T0(2):E(_ih):new T0(2);}));}),_it=function(_iu){return E(_ig);};return function(_iv){return new F(function(){return A2(_gm,_iv,_it);});};},_iw=function(_ix,_iy){var _iz=function(_iA){var _iB=new T(function(){return B(A1(_ix,_iA));}),_iC=function(_iD){return new F(function(){return _64(B(A1(_iB,_iD)),new T(function(){return new T1(1,B(_id(_iz,_iD)));}));});};return E(_iC);},_iE=new T(function(){return B(A1(_ix,_iy));}),_iF=function(_iG){return new F(function(){return _64(B(A1(_iE,_iG)),new T(function(){return new T1(1,B(_id(_iz,_iG)));}));});};return E(_iF);},_iH=function(_iI,_iJ){var _iK=function(_iL,_iM){var _iN=function(_iO){return new F(function(){return A1(_iM,new T(function(){return  -E(_iO);}));});},_iP=new T(function(){return B(_hF(function(_iQ){return new F(function(){return A3(_iI,_iQ,_iL,_iN);});}));}),_iR=function(_iS){return E(_iP);},_iT=function(_iU){return new F(function(){return A2(_gm,_iU,_iR);});},_iV=new T(function(){return B(_hF(function(_iW){var _iX=E(_iW);if(_iX._==4){var _iY=E(_iX.a);if(!_iY._){return new F(function(){return A3(_iI,_iX,_iL,_iM);});}else{if(E(_iY.a)==45){if(!E(_iY.b)._){return E(new T1(1,_iT));}else{return new F(function(){return A3(_iI,_iX,_iL,_iM);});}}else{return new F(function(){return A3(_iI,_iX,_iL,_iM);});}}}else{return new F(function(){return A3(_iI,_iX,_iL,_iM);});}}));}),_iZ=function(_j0){return E(_iV);};return new T1(1,function(_j1){return new F(function(){return A2(_gm,_j1,_iZ);});});};return new F(function(){return _iw(_iK,_iJ);});},_j2=new T(function(){return 1/0;}),_j3=function(_j4,_j5){return new F(function(){return A1(_j5,_j2);});},_j6=new T(function(){return 0/0;}),_j7=function(_j8,_j9){return new F(function(){return A1(_j9,_j6);});},_ja=new T(function(){return B(unCStr("NaN"));}),_jb=new T(function(){return B(unCStr("Infinity"));}),_jc=1024,_jd=-1021,_je=new T(function(){return B(unCStr("GHC.Exception"));}),_jf=new T(function(){return B(unCStr("base"));}),_jg=new T(function(){return B(unCStr("ArithException"));}),_jh=new T(function(){var _ji=hs_wordToWord64(new Long(4194982440,719304104,true)),_jj=hs_wordToWord64(new Long(3110813675,1843557400,true));return new T5(0,_ji,_jj,new T5(0,_ji,_jj,_jf,_je,_jg),_v,_v);}),_jk=function(_jl){return E(_jh);},_jm=function(_jn){var _jo=E(_jn);return new F(function(){return _D(B(_B(_jo.a)),_jk,_jo.b);});},_jp=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_jq=new T(function(){return B(unCStr("denormal"));}),_jr=new T(function(){return B(unCStr("divide by zero"));}),_js=new T(function(){return B(unCStr("loss of precision"));}),_jt=new T(function(){return B(unCStr("arithmetic underflow"));}),_ju=new T(function(){return B(unCStr("arithmetic overflow"));}),_jv=function(_jw,_jx){switch(E(_jw)){case 0:return new F(function(){return _R(_ju,_jx);});break;case 1:return new F(function(){return _R(_jt,_jx);});break;case 2:return new F(function(){return _R(_js,_jx);});break;case 3:return new F(function(){return _R(_jr,_jx);});break;case 4:return new F(function(){return _R(_jq,_jx);});break;default:return new F(function(){return _R(_jp,_jx);});}},_jy=function(_jz){return new F(function(){return _jv(_jz,_v);});},_jA=function(_jB,_jC,_jD){return new F(function(){return _jv(_jC,_jD);});},_jE=function(_jF,_jG){return new F(function(){return _1V(_jv,_jF,_jG);});},_jH=new T3(0,_jA,_jy,_jE),_jI=new T(function(){return new T5(0,_jk,_jH,_jJ,_jm,_jy);}),_jJ=function(_5u){return new T2(0,_jI,_5u);},_jK=3,_jL=new T(function(){return B(_jJ(_jK));}),_jM=new T(function(){return die(_jL);}),_jN=function(_jO,_jP){var _jQ=E(_jO);if(!_jQ._){var _jR=_jQ.a,_jS=E(_jP);return (_jS._==0)?_jR==_jS.a:(I_compareInt(_jS.a,_jR)==0)?true:false;}else{var _jT=_jQ.a,_jU=E(_jP);return (_jU._==0)?(I_compareInt(_jT,_jU.a)==0)?true:false:(I_compare(_jT,_jU.a)==0)?true:false;}},_jV=new T1(0,0),_jW=function(_jX,_jY){while(1){var _jZ=E(_jX);if(!_jZ._){var _k0=E(_jZ.a);if(_k0==(-2147483648)){_jX=new T1(1,I_fromInt(-2147483648));continue;}else{var _k1=E(_jY);if(!_k1._){return new T1(0,_k0%_k1.a);}else{_jX=new T1(1,I_fromInt(_k0));_jY=_k1;continue;}}}else{var _k2=_jZ.a,_k3=E(_jY);return (_k3._==0)?new T1(1,I_rem(_k2,I_fromInt(_k3.a))):new T1(1,I_rem(_k2,_k3.a));}}},_k4=function(_k5,_k6){if(!B(_jN(_k6,_jV))){return new F(function(){return _jW(_k5,_k6);});}else{return E(_jM);}},_k7=function(_k8,_k9){while(1){if(!B(_jN(_k9,_jV))){var _ka=_k9,_kb=B(_k4(_k8,_k9));_k8=_ka;_k9=_kb;continue;}else{return E(_k8);}}},_kc=function(_kd){var _ke=E(_kd);if(!_ke._){var _kf=E(_ke.a);return (_kf==(-2147483648))?E(_9h):(_kf<0)?new T1(0, -_kf):E(_ke);}else{var _kg=_ke.a;return (I_compareInt(_kg,0)>=0)?E(_ke):new T1(1,I_negate(_kg));}},_kh=function(_ki,_kj){while(1){var _kk=E(_ki);if(!_kk._){var _kl=E(_kk.a);if(_kl==(-2147483648)){_ki=new T1(1,I_fromInt(-2147483648));continue;}else{var _km=E(_kj);if(!_km._){return new T1(0,quot(_kl,_km.a));}else{_ki=new T1(1,I_fromInt(_kl));_kj=_km;continue;}}}else{var _kn=_kk.a,_ko=E(_kj);return (_ko._==0)?new T1(0,I_toInt(I_quot(_kn,I_fromInt(_ko.a)))):new T1(1,I_quot(_kn,_ko.a));}}},_kp=5,_kq=new T(function(){return B(_jJ(_kp));}),_kr=new T(function(){return die(_kq);}),_ks=function(_kt,_ku){if(!B(_jN(_ku,_jV))){var _kv=B(_k7(B(_kc(_kt)),B(_kc(_ku))));return (!B(_jN(_kv,_jV)))?new T2(0,B(_kh(_kt,_kv)),B(_kh(_ku,_kv))):E(_jM);}else{return E(_kr);}},_kw=new T1(0,1),_kx=new T(function(){return B(unCStr("Negative exponent"));}),_ky=new T(function(){return B(err(_kx));}),_kz=new T1(0,2),_kA=new T(function(){return B(_jN(_kz,_jV));}),_kB=function(_kC,_kD){while(1){var _kE=E(_kC);if(!_kE._){var _kF=_kE.a,_kG=E(_kD);if(!_kG._){var _kH=_kG.a,_kI=subC(_kF,_kH);if(!E(_kI.b)){return new T1(0,_kI.a);}else{_kC=new T1(1,I_fromInt(_kF));_kD=new T1(1,I_fromInt(_kH));continue;}}else{_kC=new T1(1,I_fromInt(_kF));_kD=_kG;continue;}}else{var _kJ=E(_kD);if(!_kJ._){_kC=_kE;_kD=new T1(1,I_fromInt(_kJ.a));continue;}else{return new T1(1,I_sub(_kE.a,_kJ.a));}}}},_kK=function(_kL,_kM,_kN){while(1){if(!E(_kA)){if(!B(_jN(B(_jW(_kM,_kz)),_jV))){if(!B(_jN(_kM,_kw))){var _kO=B(_9C(_kL,_kL)),_kP=B(_kh(B(_kB(_kM,_kw)),_kz)),_kQ=B(_9C(_kL,_kN));_kL=_kO;_kM=_kP;_kN=_kQ;continue;}else{return new F(function(){return _9C(_kL,_kN);});}}else{var _kO=B(_9C(_kL,_kL)),_kP=B(_kh(_kM,_kz));_kL=_kO;_kM=_kP;continue;}}else{return E(_jM);}}},_kR=function(_kS,_kT){while(1){if(!E(_kA)){if(!B(_jN(B(_jW(_kT,_kz)),_jV))){if(!B(_jN(_kT,_kw))){return new F(function(){return _kK(B(_9C(_kS,_kS)),B(_kh(B(_kB(_kT,_kw)),_kz)),_kS);});}else{return E(_kS);}}else{var _kU=B(_9C(_kS,_kS)),_kV=B(_kh(_kT,_kz));_kS=_kU;_kT=_kV;continue;}}else{return E(_jM);}}},_kW=function(_kX,_kY){var _kZ=E(_kX);if(!_kZ._){var _l0=_kZ.a,_l1=E(_kY);return (_l1._==0)?_l0<_l1.a:I_compareInt(_l1.a,_l0)>0;}else{var _l2=_kZ.a,_l3=E(_kY);return (_l3._==0)?I_compareInt(_l2,_l3.a)<0:I_compare(_l2,_l3.a)<0;}},_l4=function(_l5,_l6){if(!B(_kW(_l6,_jV))){if(!B(_jN(_l6,_jV))){return new F(function(){return _kR(_l5,_l6);});}else{return E(_kw);}}else{return E(_ky);}},_l7=new T1(0,1),_l8=new T1(0,0),_l9=new T1(0,-1),_la=function(_lb){var _lc=E(_lb);if(!_lc._){var _ld=_lc.a;return (_ld>=0)?(E(_ld)==0)?E(_l8):E(_96):E(_l9);}else{var _le=I_compareInt(_lc.a,0);return (_le<=0)?(E(_le)==0)?E(_l8):E(_l9):E(_96);}},_lf=function(_lg,_lh,_li){while(1){var _lj=E(_li);if(!_lj._){if(!B(_kW(_lg,_9P))){return new T2(0,B(_9C(_lh,B(_l4(_9m,_lg)))),_kw);}else{var _lk=B(_l4(_9m,B(_9i(_lg))));return new F(function(){return _ks(B(_9C(_lh,B(_la(_lk)))),B(_kc(_lk)));});}}else{var _ll=B(_kB(_lg,_l7)),_lm=B(_98(B(_9C(_lh,_9m)),B(_9w(E(_lj.a)))));_lg=_ll;_lh=_lm;_li=_lj.b;continue;}}},_ln=function(_lo,_lp){var _lq=E(_lo);if(!_lq._){var _lr=_lq.a,_ls=E(_lp);return (_ls._==0)?_lr>=_ls.a:I_compareInt(_ls.a,_lr)<=0;}else{var _lt=_lq.a,_lu=E(_lp);return (_lu._==0)?I_compareInt(_lt,_lu.a)>=0:I_compare(_lt,_lu.a)>=0;}},_lv=function(_lw){var _lx=E(_lw);if(!_lx._){var _ly=_lx.b;return new F(function(){return _ks(B(_9C(B(_9Q(new T(function(){return B(_9w(E(_lx.a)));}),new T(function(){return B(_9n(_ly,0));},1),B(_9s(_9y,_ly)))),_l7)),_l7);});}else{var _lz=_lx.a,_lA=_lx.c,_lB=E(_lx.b);if(!_lB._){var _lC=E(_lA);if(!_lC._){return new F(function(){return _ks(B(_9C(B(_a7(_9m,_lz)),_l7)),_l7);});}else{var _lD=_lC.a;if(!B(_ln(_lD,_9P))){var _lE=B(_l4(_9m,B(_9i(_lD))));return new F(function(){return _ks(B(_9C(B(_a7(_9m,_lz)),B(_la(_lE)))),B(_kc(_lE)));});}else{return new F(function(){return _ks(B(_9C(B(_9C(B(_a7(_9m,_lz)),B(_l4(_9m,_lD)))),_l7)),_l7);});}}}else{var _lF=_lB.a,_lG=E(_lA);if(!_lG._){return new F(function(){return _lf(_9P,B(_a7(_9m,_lz)),_lF);});}else{return new F(function(){return _lf(_lG.a,B(_a7(_9m,_lz)),_lF);});}}}},_lH=function(_lI,_lJ){while(1){var _lK=E(_lJ);if(!_lK._){return __Z;}else{if(!B(A1(_lI,_lK.a))){return E(_lK);}else{_lJ=_lK.b;continue;}}}},_lL=function(_lM,_lN){var _lO=E(_lM);if(!_lO._){var _lP=_lO.a,_lQ=E(_lN);return (_lQ._==0)?_lP>_lQ.a:I_compareInt(_lQ.a,_lP)<0;}else{var _lR=_lO.a,_lS=E(_lN);return (_lS._==0)?I_compareInt(_lR,_lS.a)>0:I_compare(_lR,_lS.a)>0;}},_lT=0,_lU=function(_lV,_lW){return E(_lV)==E(_lW);},_lX=function(_lY){return new F(function(){return _lU(_lT,_lY);});},_lZ=new T2(0,E(_9P),E(_kw)),_m0=new T1(1,_lZ),_m1=new T1(0,-2147483648),_m2=new T1(0,2147483647),_m3=function(_m4,_m5,_m6){var _m7=E(_m6);if(!_m7._){return new T1(1,new T(function(){var _m8=B(_lv(_m7));return new T2(0,E(_m8.a),E(_m8.b));}));}else{var _m9=E(_m7.c);if(!_m9._){return new T1(1,new T(function(){var _ma=B(_lv(_m7));return new T2(0,E(_ma.a),E(_ma.b));}));}else{var _mb=_m9.a;if(!B(_lL(_mb,_m2))){if(!B(_kW(_mb,_m1))){var _mc=function(_md){var _me=_md+B(_b3(_mb))|0;return (_me<=(E(_m5)+3|0))?(_me>=(E(_m4)-3|0))?new T1(1,new T(function(){var _mf=B(_lv(_m7));return new T2(0,E(_mf.a),E(_mf.b));})):E(_m0):__Z;},_mg=B(_lH(_lX,_m7.a));if(!_mg._){var _mh=E(_m7.b);if(!_mh._){return E(_m0);}else{var _mi=B(_5v(_lX,_mh.a));if(!E(_mi.b)._){return E(_m0);}else{return new F(function(){return _mc( -B(_9n(_mi.a,0)));});}}}else{return new F(function(){return _mc(B(_9n(_mg,0)));});}}else{return __Z;}}else{return __Z;}}}},_mj=function(_mk,_ml){return new T0(2);},_mm=new T1(0,1),_mn=function(_mo,_mp){var _mq=E(_mo);if(!_mq._){var _mr=_mq.a,_ms=E(_mp);if(!_ms._){var _mt=_ms.a;return (_mr!=_mt)?(_mr>_mt)?2:0:1;}else{var _mu=I_compareInt(_ms.a,_mr);return (_mu<=0)?(_mu>=0)?1:2:0;}}else{var _mv=_mq.a,_mw=E(_mp);if(!_mw._){var _mx=I_compareInt(_mv,_mw.a);return (_mx>=0)?(_mx<=0)?1:2:0;}else{var _my=I_compare(_mv,_mw.a);return (_my>=0)?(_my<=0)?1:2:0;}}},_mz=function(_mA,_mB){var _mC=E(_mA);return (_mC._==0)?_mC.a*Math.pow(2,_mB):I_toNumber(_mC.a)*Math.pow(2,_mB);},_mD=function(_mE,_mF){while(1){var _mG=E(_mE);if(!_mG._){var _mH=E(_mG.a);if(_mH==(-2147483648)){_mE=new T1(1,I_fromInt(-2147483648));continue;}else{var _mI=E(_mF);if(!_mI._){var _mJ=_mI.a;return new T2(0,new T1(0,quot(_mH,_mJ)),new T1(0,_mH%_mJ));}else{_mE=new T1(1,I_fromInt(_mH));_mF=_mI;continue;}}}else{var _mK=E(_mF);if(!_mK._){_mE=_mG;_mF=new T1(1,I_fromInt(_mK.a));continue;}else{var _mL=I_quotRem(_mG.a,_mK.a);return new T2(0,new T1(1,_mL.a),new T1(1,_mL.b));}}}},_mM=new T1(0,0),_mN=function(_mO,_mP){while(1){var _mQ=E(_mO);if(!_mQ._){_mO=new T1(1,I_fromInt(_mQ.a));continue;}else{return new T1(1,I_shiftLeft(_mQ.a,_mP));}}},_mR=function(_mS,_mT,_mU){if(!B(_jN(_mU,_mM))){var _mV=B(_mD(_mT,_mU)),_mW=_mV.a;switch(B(_mn(B(_mN(_mV.b,1)),_mU))){case 0:return new F(function(){return _mz(_mW,_mS);});break;case 1:if(!(B(_b3(_mW))&1)){return new F(function(){return _mz(_mW,_mS);});}else{return new F(function(){return _mz(B(_98(_mW,_mm)),_mS);});}break;default:return new F(function(){return _mz(B(_98(_mW,_mm)),_mS);});}}else{return E(_jM);}},_mX=function(_mY){var _mZ=function(_n0,_n1){while(1){if(!B(_kW(_n0,_mY))){if(!B(_lL(_n0,_mY))){if(!B(_jN(_n0,_mY))){return new F(function(){return _5R("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_n1);}}else{return _n1-1|0;}}else{var _n2=B(_mN(_n0,1)),_n3=_n1+1|0;_n0=_n2;_n1=_n3;continue;}}};return new F(function(){return _mZ(_96,0);});},_n4=function(_n5){var _n6=E(_n5);if(!_n6._){var _n7=_n6.a>>>0;if(!_n7){return -1;}else{var _n8=function(_n9,_na){while(1){if(_n9>=_n7){if(_n9<=_n7){if(_n9!=_n7){return new F(function(){return _5R("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");});}else{return E(_na);}}else{return _na-1|0;}}else{var _nb=imul(_n9,2)>>>0,_nc=_na+1|0;_n9=_nb;_na=_nc;continue;}}};return new F(function(){return _n8(1,0);});}}else{return new F(function(){return _mX(_n6);});}},_nd=function(_ne){var _nf=E(_ne);if(!_nf._){var _ng=_nf.a>>>0;if(!_ng){return new T2(0,-1,0);}else{var _nh=function(_ni,_nj){while(1){if(_ni>=_ng){if(_ni<=_ng){if(_ni!=_ng){return new F(function(){return _5R("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");});}else{return E(_nj);}}else{return _nj-1|0;}}else{var _nk=imul(_ni,2)>>>0,_nl=_nj+1|0;_ni=_nk;_nj=_nl;continue;}}};return new T2(0,B(_nh(1,0)),(_ng&_ng-1>>>0)>>>0&4294967295);}}else{var _nm=B(_n4(_nf)),_nn=_nm>>>0;if(!_nn){var _no=E(_nm);return (_no==(-2))?new T2(0,-2,0):new T2(0,_no,1);}else{var _np=function(_nq,_nr){while(1){if(_nq>=_nn){if(_nq<=_nn){if(_nq!=_nn){return new F(function(){return _5R("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");});}else{return E(_nr);}}else{return _nr-1|0;}}else{var _ns=imul(_nq,2)>>>0,_nt=_nr+1|0;_nq=_ns;_nr=_nt;continue;}}},_nu=B(_np(1,0));return ((_nu+_nu|0)!=_nm)?new T2(0,_nm,1):new T2(0,_nm,0);}}},_nv=function(_nw,_nx){while(1){var _ny=E(_nw);if(!_ny._){var _nz=_ny.a,_nA=E(_nx);if(!_nA._){return new T1(0,(_nz>>>0&_nA.a>>>0)>>>0&4294967295);}else{_nw=new T1(1,I_fromInt(_nz));_nx=_nA;continue;}}else{var _nB=E(_nx);if(!_nB._){_nw=_ny;_nx=new T1(1,I_fromInt(_nB.a));continue;}else{return new T1(1,I_and(_ny.a,_nB.a));}}}},_nC=new T1(0,2),_nD=function(_nE,_nF){var _nG=E(_nE);if(!_nG._){var _nH=(_nG.a>>>0&(2<<_nF>>>0)-1>>>0)>>>0,_nI=1<<_nF>>>0;return (_nI<=_nH)?(_nI>=_nH)?1:2:0;}else{var _nJ=B(_nv(_nG,B(_kB(B(_mN(_nC,_nF)),_96)))),_nK=B(_mN(_96,_nF));return (!B(_lL(_nK,_nJ)))?(!B(_kW(_nK,_nJ)))?1:2:0;}},_nL=function(_nM,_nN){while(1){var _nO=E(_nM);if(!_nO._){_nM=new T1(1,I_fromInt(_nO.a));continue;}else{return new T1(1,I_shiftRight(_nO.a,_nN));}}},_nP=function(_nQ,_nR,_nS,_nT){var _nU=B(_nd(_nT)),_nV=_nU.a;if(!E(_nU.b)){var _nW=B(_n4(_nS));if(_nW<((_nV+_nQ|0)-1|0)){var _nX=_nV+(_nQ-_nR|0)|0;if(_nX>0){if(_nX>_nW){if(_nX<=(_nW+1|0)){if(!E(B(_nd(_nS)).b)){return 0;}else{return new F(function(){return _mz(_mm,_nQ-_nR|0);});}}else{return 0;}}else{var _nY=B(_nL(_nS,_nX));switch(B(_nD(_nS,_nX-1|0))){case 0:return new F(function(){return _mz(_nY,_nQ-_nR|0);});break;case 1:if(!(B(_b3(_nY))&1)){return new F(function(){return _mz(_nY,_nQ-_nR|0);});}else{return new F(function(){return _mz(B(_98(_nY,_mm)),_nQ-_nR|0);});}break;default:return new F(function(){return _mz(B(_98(_nY,_mm)),_nQ-_nR|0);});}}}else{return new F(function(){return _mz(_nS,(_nQ-_nR|0)-_nX|0);});}}else{if(_nW>=_nR){var _nZ=B(_nL(_nS,(_nW+1|0)-_nR|0));switch(B(_nD(_nS,_nW-_nR|0))){case 0:return new F(function(){return _mz(_nZ,((_nW-_nV|0)+1|0)-_nR|0);});break;case 2:return new F(function(){return _mz(B(_98(_nZ,_mm)),((_nW-_nV|0)+1|0)-_nR|0);});break;default:if(!(B(_b3(_nZ))&1)){return new F(function(){return _mz(_nZ,((_nW-_nV|0)+1|0)-_nR|0);});}else{return new F(function(){return _mz(B(_98(_nZ,_mm)),((_nW-_nV|0)+1|0)-_nR|0);});}}}else{return new F(function(){return _mz(_nS, -_nV);});}}}else{var _o0=B(_n4(_nS))-_nV|0,_o1=function(_o2){var _o3=function(_o4,_o5){if(!B(_b6(B(_mN(_o5,_nR)),_o4))){return new F(function(){return _mR(_o2-_nR|0,_o4,_o5);});}else{return new F(function(){return _mR((_o2-_nR|0)+1|0,_o4,B(_mN(_o5,1)));});}};if(_o2>=_nR){if(_o2!=_nR){return new F(function(){return _o3(_nS,new T(function(){return B(_mN(_nT,_o2-_nR|0));}));});}else{return new F(function(){return _o3(_nS,_nT);});}}else{return new F(function(){return _o3(new T(function(){return B(_mN(_nS,_nR-_o2|0));}),_nT);});}};if(_nQ>_o0){return new F(function(){return _o1(_nQ);});}else{return new F(function(){return _o1(_o0);});}}},_o6=new T(function(){return 0/0;}),_o7=new T(function(){return -1/0;}),_o8=new T(function(){return 1/0;}),_o9=0,_oa=function(_ob,_oc){if(!B(_jN(_oc,_mM))){if(!B(_jN(_ob,_mM))){if(!B(_kW(_ob,_mM))){return new F(function(){return _nP(-1021,53,_ob,_oc);});}else{return  -B(_nP(-1021,53,B(_9i(_ob)),_oc));}}else{return E(_o9);}}else{return (!B(_jN(_ob,_mM)))?(!B(_kW(_ob,_mM)))?E(_o8):E(_o7):E(_o6);}},_od=function(_oe){var _of=E(_oe);switch(_of._){case 3:var _og=_of.a;return (!B(_6I(_og,_jb)))?(!B(_6I(_og,_ja)))?E(_mj):E(_j7):E(_j3);case 5:var _oh=B(_m3(_jd,_jc,_of.a));if(!_oh._){return E(_j3);}else{var _oi=new T(function(){var _oj=E(_oh.a);return B(_oa(_oj.a,_oj.b));});return function(_ok,_ol){return new F(function(){return A1(_ol,_oi);});};}break;default:return E(_mj);}},_om=function(_on){var _oo=function(_op){return E(new T2(3,_on,_7e));};return new T1(1,function(_oq){return new F(function(){return A2(_gm,_oq,_oo);});});},_or=new T(function(){return B(A3(_iH,_od,_ic,_om));}),_os=new T(function(){return B(unCStr("height"));}),_ot=function(_ou){while(1){var _ov=B((function(_ow){var _ox=E(_ow);if(!_ox._){return __Z;}else{var _oy=_ox.b,_oz=E(_ox.a);if(!E(_oz.b)._){return new T2(1,_oz.a,new T(function(){return B(_ot(_oy));}));}else{_ou=_oy;return __continue;}}})(_ou));if(_ov!=__continue){return _ov;}}},_oA=function(_oB,_){var _oC=B(A(_4I,[_4p,_2v,_oB,_4S,_])),_oD=B(A(_4I,[_4p,_2v,_oB,_os,_]));return new T2(0,new T(function(){var _oE=B(_ot(B(_5U(_or,_oC))));if(!_oE._){return E(_4W);}else{if(!E(_oE.b)._){return E(_oE.a);}else{return E(_4U);}}}),new T(function(){var _oF=B(_ot(B(_5U(_or,_oD))));if(!_oF._){return E(_4W);}else{if(!E(_oF.b)._){return E(_oF.a);}else{return E(_4U);}}}));},_oG=function(_oH,_oI,_oJ,_oK){var _oL=new T(function(){var _oM=E(E(_oI).a),_oN=E(_oK),_oO=E(E(_oJ).a)*0.95,_oP=E(_oN.a)*E(_oN.b);if(_oM+_oO>=_oP){var _oQ=E(E(_oH).a)-_oP;if(_oM+_oO<=_oQ){return new T2(0,_oM+_oO,_oO);}else{return new T2(0,_oQ+_oQ-(_oM+_oO), -_oO);}}else{return new T2(0,_oP+_oP-(_oM+_oO), -_oO);}}),_oR=new T(function(){var _oS=E(E(_oI).b),_oT=E(_oK),_oU=E(E(_oJ).b)*0.95,_oV=E(_oT.a)*E(_oT.b);if(_oS+_oU>=_oV){var _oW=E(E(_oH).b)-_oV;if(_oS+_oU<=_oW){return new T2(0,_oS+_oU,_oU);}else{return new T2(0,_oW+_oW-(_oS+_oU), -_oU);}}else{return new T2(0,_oV+_oV-(_oS+_oU), -_oU);}});return new T3(0,new T2(0,new T(function(){return E(E(_oL).a);}),new T(function(){return E(E(_oR).a);})),new T2(0,new T(function(){return E(E(_oL).b);}),new T(function(){return E(E(_oR).b);})),_oK);},_oX=function(_oY,_oZ){var _p0=E(_oZ),_p1=B(_oG(_oY,_p0.a,_p0.b,_p0.c));return new T3(0,_p1.a,_p1.b,_p1.c);},_p2=function(_p3,_p4,_p5){var _p6=E(_p5);if(!_p6._){return new T2(1,new T(function(){return B(_oX(_p3,_p4));}),_v);}else{var _p7=new T(function(){var _p8=E(_p4),_p9=_p8.b,_pa=E(_p8.c),_pb=E(_pa.a),_pc=E(_pa.b),_pd=E(_p6.a),_pe=_pd.b,_pf=E(_pd.c),_pg=E(_pf.a),_ph=E(_pf.b),_pi=E(_p8.a),_pj=E(_pd.a);if(_pb*_pc+_pg*_ph>=Math.sqrt(Math.pow(E(_pi.a)-E(_pj.a),2)+Math.pow(E(_pi.b)-E(_pj.b),2))){var _pk=new T(function(){var _pl=E(_pe),_pm=E(_p9);return new T2(0,new T(function(){var _pn=E(_pl.a);return _pn+ -((_pn+ -E(_pm.a))*1.05);}),new T(function(){var _po=E(_pl.b);return _po+ -((_po+ -E(_pm.b))*1.05);}));}),_pp=new T(function(){var _pq=E(_p9),_pr=E(_pe);return new T2(0,new T(function(){var _ps=E(_pq.a);return _ps+ -((_ps+ -E(_pr.a))*1.05);}),new T(function(){var _pt=E(_pq.b);return _pt+ -((_pt+ -E(_pr.b))*1.05);}));});return new T2(0,new T3(0,_pi,_pp,new T5(0,_pb,_pc,_pa.c,new T(function(){return E(_pa.d)+1|0;}),_pa.e)),new T3(0,_pj,_pk,new T5(0,_pg,_ph,_pf.c,new T(function(){return E(_pf.d)+1|0;}),_pf.e)));}else{return new T2(0,_p8,_pd);}}),_pu=new T(function(){return B(_p2(_p3,new T(function(){return E(E(_p7).b);}),_p6.b));});return new T2(1,new T(function(){var _pv=E(E(_p7).a),_pw=B(_oG(_p3,_pv.a,_pv.b,_pv.c));return new T3(0,_pw.a,_pw.b,_pw.c);}),_pu);}},_px=function(_py,_pz){var _pA=E(_pz);if(!_pA._){return __Z;}else{var _pB=_pA.a,_pC=E(_pA.b);if(!_pC._){return new T2(1,new T(function(){return B(_oX(_py,_pB));}),_v);}else{var _pD=new T(function(){var _pE=E(_pB),_pF=_pE.b,_pG=E(_pE.c),_pH=E(_pG.a),_pI=E(_pG.b),_pJ=E(_pC.a),_pK=_pJ.b,_pL=E(_pJ.c),_pM=E(_pL.a),_pN=E(_pL.b),_pO=E(_pE.a),_pP=E(_pJ.a);if(_pH*_pI+_pM*_pN>=Math.sqrt(Math.pow(E(_pO.a)-E(_pP.a),2)+Math.pow(E(_pO.b)-E(_pP.b),2))){var _pQ=new T(function(){var _pR=E(_pK),_pS=E(_pF);return new T2(0,new T(function(){var _pT=E(_pR.a);return _pT+ -((_pT+ -E(_pS.a))*1.05);}),new T(function(){var _pU=E(_pR.b);return _pU+ -((_pU+ -E(_pS.b))*1.05);}));}),_pV=new T(function(){var _pW=E(_pF),_pX=E(_pK);return new T2(0,new T(function(){var _pY=E(_pW.a);return _pY+ -((_pY+ -E(_pX.a))*1.05);}),new T(function(){var _pZ=E(_pW.b);return _pZ+ -((_pZ+ -E(_pX.b))*1.05);}));});return new T2(0,new T3(0,_pO,_pV,new T5(0,_pH,_pI,_pG.c,new T(function(){return E(_pG.d)+1|0;}),_pG.e)),new T3(0,_pP,_pQ,new T5(0,_pM,_pN,_pL.c,new T(function(){return E(_pL.d)+1|0;}),_pL.e)));}else{return new T2(0,_pE,_pJ);}}),_q0=new T(function(){return B(_p2(_py,new T(function(){return E(E(_pD).b);}),_pC.b));});return new T2(1,new T(function(){var _q1=E(E(_pD).a),_q2=B(_oG(_py,_q1.a,_q1.b,_q1.c));return new T3(0,_q2.a,_q2.b,_q2.c);}),_q0);}}},_q3=function(_q4){return E(E(_q4).a);},_q5=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_q6=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_q7=function(_q8){return E(E(_q8).b);},_q9=function(_qa,_qb,_qc){var _qd=B(_q3(_qa)),_qe=new T(function(){return B(_2D(_qd));}),_qf=function(_qg){var _qh=function(_){var _qi=E(_qb);if(!_qi._){var _qj=B(A1(_qg,_2Q)),_qk=__createJSFunc(0,function(_){var _ql=B(A1(_qj,_));return _2C;}),_qm=__app2(E(_q6),_qi.a,_qk);return new T(function(){var _qn=Number(_qm),_qo=jsTrunc(_qn);return new T2(0,_qo,E(_qi));});}else{var _qp=B(A1(_qg,_2Q)),_qq=__createJSFunc(0,function(_){var _qr=B(A1(_qp,_));return _2C;}),_qs=__app2(E(_q5),_qi.a,_qq);return new T(function(){var _qt=Number(_qs),_qu=jsTrunc(_qt);return new T2(0,_qu,E(_qi));});}};return new F(function(){return A1(_qe,_qh);});},_qv=new T(function(){return B(A2(_q7,_qa,function(_qw){return E(_qc);}));});return new F(function(){return A3(_4s,B(_4q(_qd)),_qv,_qf);});},_qx=function(_qy){return E(E(_qy).b);},_qz=new T2(1,_v,_v),_qA=function(_qB,_qC){var _qD=function(_qE,_qF){var _qG=E(_qE);if(!_qG._){return E(_qF);}else{var _qH=_qG.a,_qI=E(_qF);if(!_qI._){return E(_qG);}else{var _qJ=_qI.a;return (B(A2(_qB,_qH,_qJ))==2)?new T2(1,_qJ,new T(function(){return B(_qD(_qG,_qI.b));})):new T2(1,_qH,new T(function(){return B(_qD(_qG.b,_qI));}));}}},_qK=function(_qL){var _qM=E(_qL);if(!_qM._){return __Z;}else{var _qN=E(_qM.b);return (_qN._==0)?E(_qM):new T2(1,new T(function(){return B(_qD(_qM.a,_qN.a));}),new T(function(){return B(_qK(_qN.b));}));}},_qO=new T(function(){return B(_qP(B(_qK(_v))));}),_qP=function(_qQ){while(1){var _qR=E(_qQ);if(!_qR._){return E(_qO);}else{if(!E(_qR.b)._){return E(_qR.a);}else{_qQ=B(_qK(_qR));continue;}}}},_qS=new T(function(){return B(_qT(_v));}),_qU=function(_qV,_qW,_qX){while(1){var _qY=B((function(_qZ,_r0,_r1){var _r2=E(_r1);if(!_r2._){return new T2(1,new T2(1,_qZ,_r0),_qS);}else{var _r3=_r2.a;if(B(A2(_qB,_qZ,_r3))==2){var _r4=new T2(1,_qZ,_r0);_qV=_r3;_qW=_r4;_qX=_r2.b;return __continue;}else{return new T2(1,new T2(1,_qZ,_r0),new T(function(){return B(_qT(_r2));}));}}})(_qV,_qW,_qX));if(_qY!=__continue){return _qY;}}},_r5=function(_r6,_r7,_r8){while(1){var _r9=B((function(_ra,_rb,_rc){var _rd=E(_rc);if(!_rd._){return new T2(1,new T(function(){return B(A1(_rb,new T2(1,_ra,_v)));}),_qS);}else{var _re=_rd.a,_rf=_rd.b;switch(B(A2(_qB,_ra,_re))){case 0:_r6=_re;_r7=function(_rg){return new F(function(){return A1(_rb,new T2(1,_ra,_rg));});};_r8=_rf;return __continue;case 1:_r6=_re;_r7=function(_rh){return new F(function(){return A1(_rb,new T2(1,_ra,_rh));});};_r8=_rf;return __continue;default:return new T2(1,new T(function(){return B(A1(_rb,new T2(1,_ra,_v)));}),new T(function(){return B(_qT(_rd));}));}}})(_r6,_r7,_r8));if(_r9!=__continue){return _r9;}}},_qT=function(_ri){var _rj=E(_ri);if(!_rj._){return E(_qz);}else{var _rk=_rj.a,_rl=E(_rj.b);if(!_rl._){return new T2(1,_rj,_v);}else{var _rm=_rl.a,_rn=_rl.b;if(B(A2(_qB,_rk,_rm))==2){return new F(function(){return _qU(_rm,new T2(1,_rk,_v),_rn);});}else{return new F(function(){return _r5(_rm,function(_ro){return new T2(1,_rk,_ro);},_rn);});}}}};return new F(function(){return _qP(B(_qT(_qC)));});},_rp=function(_rq,_rr,_rs,_){var _rt=E(_3u),_ru=__app1(_rt,_rr),_rv=function(_rw,_rx,_){var _ry=E(_rw);if(!_ry._){return _v;}else{var _rz=E(_ry.a),_rA=_rz.a,_rB=E(_rz.c),_rC=_rB.a,_rD=_rB.b,_rE=function(_){var _rF=new T(function(){var _rG=E(_rA);return B(_3n(_rG.a,_rG.b,new T(function(){return B(_3h(0,E(_rB.d),_v));},1)));}),_rH=B(A(_3K,[_46,_rF,_rx,_])),_rI=B(_rv(_ry.b,_rx,_));return new T2(1,_rH,_rI);};if(!E(_rB.e)){var _rJ=new T(function(){return E(_rC)*E(_rD);}),_rK=function(_rL,_){var _rM=E(_rA);return new F(function(){return _2W(E(_rM.a),E(_rM.b),E(_rJ),E(_rL),_);});},_rN=B(A(_3K,[_44,function(_rO,_){return new F(function(){return _35(_rK,E(_rO),_);});},_rx,_]));return new F(function(){return _rE(_);});}else{var _rP=new T(function(){return E(_rC)*E(_rD);}),_rQ=function(_rR,_){var _rS=E(_rA);return new F(function(){return _2W(E(_rS.a),E(_rS.b),E(_rP),E(_rR),_);});},_rT=B(A(_3K,[_45,function(_rU,_){return new F(function(){return _35(_rQ,E(_rU),_);});},_rx,_]));return new F(function(){return _rE(_);});}}},_rV=B(_rv(_rs,_rq,_)),_rW=B(_oA(new T2(0,_rq,_rr),_)),_rX=_rW,_rY=function(_){var _rZ=function(_s0,_s1,_){var _s2=E(_s0);if(!_s2._){return _v;}else{var _s3=E(_s2.a),_s4=_s3.a,_s5=E(_s3.c),_s6=_s5.a,_s7=_s5.b,_s8=function(_){var _s9=new T(function(){var _sa=E(_s4);return B(_3n(_sa.a,_sa.b,new T(function(){return B(_3h(0,E(_s5.d),_v));},1)));}),_sb=B(A(_3K,[_46,_s9,_s1,_])),_sc=B(_rZ(_s2.b,_s1,_));return new T2(1,_sb,_sc);};if(!E(_s5.e)){var _sd=new T(function(){return E(_s6)*E(_s7);}),_se=function(_sf,_){var _sg=E(_s4);return new F(function(){return _2W(E(_sg.a),E(_sg.b),E(_sd),E(_sf),_);});},_sh=B(A(_3K,[_44,function(_si,_){return new F(function(){return _35(_se,E(_si),_);});},_s1,_]));return new F(function(){return _s8(_);});}else{var _sj=new T(function(){return E(_s6)*E(_s7);}),_sk=function(_sl,_){var _sm=E(_s4);return new F(function(){return _2W(E(_sm.a),E(_sm.b),E(_sj),E(_sl),_);});},_sn=B(A(_3K,[_45,function(_so,_){return new F(function(){return _35(_sk,E(_so),_);});},_s1,_]));return new F(function(){return _s8(_);});}}},_sp=function(_sq,_sr,_ss,_){var _st=__app1(_rt,_sr),_su=B(_rZ(_ss,_sq,_)),_sv=B(_oA(new T2(0,_sq,_sr),_)),_sw=_sv,_sx=function(_){return new F(function(){return _sp(_sq,_sr,new T(function(){return B(_px(_sw,B(_9s(_qx,B(_qA(_4c,B(_9s(_48,_ss))))))));}),_);});},_sy=B(A(_q9,[_2P,_47,_sx,_]));return _2Q;};return new F(function(){return _sp(_rq,_rr,new T(function(){return B(_px(_rX,B(_9s(_qx,B(_qA(_4c,B(_9s(_48,_rs))))))));}),_);});},_sz=B(A(_q9,[_2P,_47,_rY,_]));return _2Q;},_sA=function(_sB,_sC){var _sD=new T(function(){var _sE=B(_sA(_sB,new T(function(){return B(A1(_sB,_sC));})));return new T2(1,_sE.a,_sE.b);});return new T2(0,_sC,_sD);},_sF=new T(function(){return B(unCStr("Pattern match failure in do expression at barshare.hs:117:3-10"));}),_sG=new T6(0,_2d,_2e,_v,_sF,_2d,_2d),_sH=new T(function(){return B(_1G(_sG));}),_sI=100,_sJ=new T2(0,_sI,_sI),_sK=1,_sL=1,_sM=new T(function(){return B(unCStr("banana"));}),_sN=7,_sO=9,_sP=new T5(0,_sO,_sN,_sM,_sL,_sK),_sQ=function(_sR){var _sS=E(_sR);return (_sS==1)?new T2(0,_sP,_v):new T2(0,_sP,new T(function(){var _sT=B(_sQ(_sS-1|0));return new T2(1,_sT.a,_sT.b);}));},_sU=new T(function(){var _sV=B(_sQ(10));return new T2(1,_sV.a,_sV.b);}),_sW=new T(function(){return B(_9n(_sU,0));}),_sX=function(_sY,_sZ){return E(_sY)+E(_sZ);},_t0=function(_,_t1){var _t2=E(_t1);if(!_t2._){return new F(function(){return die(_sH);});}else{var _t3=_t2.a,_t4=B(_oA(_t3,_)),_t5=E(_t4),_t6=E(_t3),_t7=new T(function(){var _t8=new T(function(){return E(_t5.b)/(E(_sW)+1);}),_t9=B(_sA(function(_ta){return new F(function(){return _sX(_ta,_t8);});},_t8)),_tb=new T(function(){return E(_t5.a)/(E(_sW)+1);}),_tc=function(_td,_te,_tf){var _tg=E(_te);if(!_tg._){return __Z;}else{var _th=E(_tf);if(!_th._){return __Z;}else{var _ti=new T(function(){return B(_tc(new T(function(){return E(_td)+E(_tb);}),_tg.b,_th.b));});return new T2(1,new T3(0,new T2(0,_td,_tg.a),_sJ,_th.a),_ti);}}},_tj=function(_tk,_tl,_tm,_tn){var _to=E(_tn);if(!_to._){return __Z;}else{var _tp=new T(function(){return B(_tc(new T(function(){return E(_tk)+E(_tb);}),_tm,_to.b));});return new T2(1,new T3(0,new T2(0,_tk,_tl),_sJ,_to.a),_tp);}};return B(_tj(_tb,_t9.a,_t9.b,_sU));});return new F(function(){return _rp(_t6.a,_t6.b,_t7,_);});}},_tq=function(_){var _tr=B(A3(_2F,_2v,_2O,_)),_ts=E(_tr);if(!_ts._){return new F(function(){return die(_2N);});}else{var _tt=E(_ts.a),_tu=__app1(E(_1),_tt);if(!_tu){return new F(function(){return _t0(_,_2d);});}else{var _tv=__app1(E(_0),_tt);return new F(function(){return _t0(_,new T1(1,new T2(0,_tv,_tt)));});}}},_tw=function(_){return new F(function(){return _tq(_);});};
var hasteMain = function() {B(A(_tw, [0]));};window.onload = hasteMain;