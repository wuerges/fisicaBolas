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

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4,_){var _5=B(A1(_3,_)),_6=B(A1(_4,_));return _5;},_7=function(_8,_9,_){var _a=B(A1(_8,_)),_b=B(A1(_9,_));return new T(function(){return B(A1(_a,_b));});},_c=function(_d,_e,_){var _f=B(A1(_e,_));return _d;},_g=function(_h,_i,_){var _j=B(A1(_i,_));return new T(function(){return B(A1(_h,_j));});},_k=new T2(0,_g,_c),_l=function(_m,_){return _m;},_n=function(_o,_p,_){var _q=B(A1(_o,_));return new F(function(){return A1(_p,_);});},_r=new T5(0,_k,_l,_7,_n,_2),_s=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_t=new T(function(){return B(unCStr("base"));}),_u=new T(function(){return B(unCStr("IOException"));}),_v=__Z,_w=new T(function(){var _x=hs_wordToWord64(new Long(4053623282,1685460941,true)),_y=hs_wordToWord64(new Long(3693590983,2507416641,true));return new T5(0,_x,_y,new T5(0,_x,_y,_t,_s,_u),_v,_v);}),_z=function(_A){return E(_w);},_B=function(_C){return E(E(_C).a);},_D=function(_E,_F,_G){var _H=B(A1(_E,_)),_I=B(A1(_F,_)),_J=hs_eqWord64(_H.a,_I.a);if(!_J){return __Z;}else{var _K=hs_eqWord64(_H.b,_I.b);return (!_K)?__Z:new T1(1,_G);}},_L=function(_M){var _N=E(_M);return new F(function(){return _D(B(_B(_N.a)),_z,_N.b);});},_O=new T(function(){return B(unCStr(": "));}),_P=new T(function(){return B(unCStr(")"));}),_Q=new T(function(){return B(unCStr(" ("));}),_R=function(_S,_T){var _U=E(_S);return (_U._==0)?E(_T):new T2(1,_U.a,new T(function(){return B(_R(_U.b,_T));}));},_V=new T(function(){return B(unCStr("interrupted"));}),_W=new T(function(){return B(unCStr("system error"));}),_X=new T(function(){return B(unCStr("unsatisified constraints"));}),_Y=new T(function(){return B(unCStr("user error"));}),_Z=new T(function(){return B(unCStr("permission denied"));}),_10=new T(function(){return B(unCStr("illegal operation"));}),_11=new T(function(){return B(unCStr("end of file"));}),_12=new T(function(){return B(unCStr("resource exhausted"));}),_13=new T(function(){return B(unCStr("resource busy"));}),_14=new T(function(){return B(unCStr("does not exist"));}),_15=new T(function(){return B(unCStr("already exists"));}),_16=new T(function(){return B(unCStr("resource vanished"));}),_17=new T(function(){return B(unCStr("timeout"));}),_18=new T(function(){return B(unCStr("unsupported operation"));}),_19=new T(function(){return B(unCStr("hardware fault"));}),_1a=new T(function(){return B(unCStr("inappropriate type"));}),_1b=new T(function(){return B(unCStr("invalid argument"));}),_1c=new T(function(){return B(unCStr("failed"));}),_1d=new T(function(){return B(unCStr("protocol error"));}),_1e=function(_1f,_1g){switch(E(_1f)){case 0:return new F(function(){return _R(_15,_1g);});break;case 1:return new F(function(){return _R(_14,_1g);});break;case 2:return new F(function(){return _R(_13,_1g);});break;case 3:return new F(function(){return _R(_12,_1g);});break;case 4:return new F(function(){return _R(_11,_1g);});break;case 5:return new F(function(){return _R(_10,_1g);});break;case 6:return new F(function(){return _R(_Z,_1g);});break;case 7:return new F(function(){return _R(_Y,_1g);});break;case 8:return new F(function(){return _R(_X,_1g);});break;case 9:return new F(function(){return _R(_W,_1g);});break;case 10:return new F(function(){return _R(_1d,_1g);});break;case 11:return new F(function(){return _R(_1c,_1g);});break;case 12:return new F(function(){return _R(_1b,_1g);});break;case 13:return new F(function(){return _R(_1a,_1g);});break;case 14:return new F(function(){return _R(_19,_1g);});break;case 15:return new F(function(){return _R(_18,_1g);});break;case 16:return new F(function(){return _R(_17,_1g);});break;case 17:return new F(function(){return _R(_16,_1g);});break;default:return new F(function(){return _R(_V,_1g);});}},_1h=new T(function(){return B(unCStr("}"));}),_1i=new T(function(){return B(unCStr("{handle: "));}),_1j=function(_1k,_1l,_1m,_1n,_1o,_1p){var _1q=new T(function(){var _1r=new T(function(){var _1s=new T(function(){var _1t=E(_1n);if(!_1t._){return E(_1p);}else{var _1u=new T(function(){return B(_R(_1t,new T(function(){return B(_R(_P,_1p));},1)));},1);return B(_R(_Q,_1u));}},1);return B(_1e(_1l,_1s));}),_1v=E(_1m);if(!_1v._){return E(_1r);}else{return B(_R(_1v,new T(function(){return B(_R(_O,_1r));},1)));}}),_1w=E(_1o);if(!_1w._){var _1x=E(_1k);if(!_1x._){return E(_1q);}else{var _1y=E(_1x.a);if(!_1y._){var _1z=new T(function(){var _1A=new T(function(){return B(_R(_1h,new T(function(){return B(_R(_O,_1q));},1)));},1);return B(_R(_1y.a,_1A));},1);return new F(function(){return _R(_1i,_1z);});}else{var _1B=new T(function(){var _1C=new T(function(){return B(_R(_1h,new T(function(){return B(_R(_O,_1q));},1)));},1);return B(_R(_1y.a,_1C));},1);return new F(function(){return _R(_1i,_1B);});}}}else{return new F(function(){return _R(_1w.a,new T(function(){return B(_R(_O,_1q));},1));});}},_1D=function(_1E){var _1F=E(_1E);return new F(function(){return _1j(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_v);});},_1G=function(_1H){return new T2(0,_1I,_1H);},_1J=function(_1K,_1L,_1M){var _1N=E(_1L);return new F(function(){return _1j(_1N.a,_1N.b,_1N.c,_1N.d,_1N.f,_1M);});},_1O=function(_1P,_1Q){var _1R=E(_1P);return new F(function(){return _1j(_1R.a,_1R.b,_1R.c,_1R.d,_1R.f,_1Q);});},_1S=44,_1T=93,_1U=91,_1V=function(_1W,_1X,_1Y){var _1Z=E(_1X);if(!_1Z._){return new F(function(){return unAppCStr("[]",_1Y);});}else{var _20=new T(function(){var _21=new T(function(){var _22=function(_23){var _24=E(_23);if(!_24._){return E(new T2(1,_1T,_1Y));}else{var _25=new T(function(){return B(A2(_1W,_24.a,new T(function(){return B(_22(_24.b));})));});return new T2(1,_1S,_25);}};return B(_22(_1Z.b));});return B(A2(_1W,_1Z.a,_21));});return new T2(1,_1U,_20);}},_26=function(_27,_28){return new F(function(){return _1V(_1O,_27,_28);});},_29=new T3(0,_1J,_1D,_26),_1I=new T(function(){return new T5(0,_z,_29,_1G,_L,_1D);}),_2a=new T(function(){return E(_1I);}),_2b=function(_2c){return E(E(_2c).c);},_2d=__Z,_2e=7,_2f=function(_2g){return new T6(0,_2d,_2e,_v,_2g,_2d,_2d);},_2h=function(_2i,_){var _2j=new T(function(){return B(A2(_2b,_2a,new T(function(){return B(A1(_2f,_2i));})));});return new F(function(){return die(_2j);});},_2k=function(_2l,_){return new F(function(){return _2h(_2l,_);});},_2m=function(_2n){return new F(function(){return A1(_2k,_2n);});},_2o=function(_2p,_2q,_){var _2r=B(A1(_2p,_));return new F(function(){return A2(_2q,_2r,_);});},_2s=new T5(0,_r,_2o,_n,_l,_2m),_2t=function(_2u){return E(_2u);},_2v=new T2(0,_2s,_2t),_2w=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_2x=function(_){return new F(function(){return __jsNull();});},_2y=function(_2z){var _2A=B(A1(_2z,_));return E(_2A);},_2B=new T(function(){return B(_2y(_2x));}),_2C=new T(function(){return E(_2B);}),_2D=function(_2E){return E(E(_2E).b);},_2F=function(_2G,_2H){var _2I=function(_){var _2J=__app1(E(_2w),E(_2H)),_2K=__eq(_2J,E(_2C));return (E(_2K)==0)?new T1(1,_2J):_2d;};return new F(function(){return A2(_2D,_2G,_2I);});},_2L=new T(function(){return B(unCStr("Pattern match failure in do expression at barshare.hs:129:3-8"));}),_2M=new T6(0,_2d,_2e,_v,_2L,_2d,_2d),_2N=new T(function(){return B(_1G(_2M));}),_2O="canvas",_2P=new T2(0,_2v,_l),_2Q=0,_2R=function(_){return _2Q;},_2S=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_2T=0,_2U=6.283185307179586,_2V=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_2W=function(_2X,_2Y,_2Z,_30,_){var _31=__app3(E(_2V),_30,_2X+_2Z,_2Y),_32=__apply(E(_2S),new T2(1,_2U,new T2(1,_2T,new T2(1,_2Z,new T2(1,_2Y,new T2(1,_2X,new T2(1,_30,_v)))))));return new F(function(){return _2R(_);});},_33=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_34=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_35=function(_36,_37,_){var _38=__app1(E(_33),_37),_39=B(A2(_36,_37,_)),_3a=__app1(E(_34),_37);return new F(function(){return _2R(_);});},_3b=function(_3c,_3d){var _3e=jsShowI(_3c);return new F(function(){return _R(fromJSStr(_3e),_3d);});},_3f=41,_3g=40,_3h=function(_3i,_3j,_3k){if(_3j>=0){return new F(function(){return _3b(_3j,_3k);});}else{if(_3i<=6){return new F(function(){return _3b(_3j,_3k);});}else{return new T2(1,_3g,new T(function(){var _3l=jsShowI(_3j);return B(_R(fromJSStr(_3l),new T2(1,_3f,_3k)));}));}}},_3m=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_3n=function(_3o,_3p,_3q){var _3r=new T(function(){return toJSStr(E(_3q));});return function(_3s,_){var _3t=__app4(E(_3m),E(_3s),E(_3r),E(_3o),E(_3p));return new F(function(){return _2R(_);});};},_3u=new T(function(){return eval("(function(e){e.width = e.width;})");}),_3v=function(_3w){var _3x=E(_3w);if(!_3x._){return __Z;}else{var _3y=_3x.a,_3z=new T(function(){var _3A=E(_3x.b);if(!_3A._){return new T2(0,_3y,_v);}else{var _3B=E(_3y),_3C=_3B.b,_3D=E(_3B.c),_3E=_3D.c,_3F=_3D.d,_3G=_3D.e,_3H=E(_3D.a),_3I=E(_3D.b),_3J=_3H*_3I,_3K=E(_3A.a),_3L=_3K.b,_3M=E(_3K.c),_3N=E(_3M.a),_3O=E(_3M.b),_3P=E(_3B.a),_3Q=E(_3K.a),_3R=E(_3P.a),_3S=E(_3Q.a),_3T=E(_3P.b),_3U=E(_3Q.b),_3V=new T(function(){var _3W=function(_3X){var _3Y=E(_3X);if(!_3Y._){return new T2(0,_v,_v);}else{var _3Z=E(_3Y.a),_40=E(_3Z.c),_41=E(_3Z.a),_42=new T(function(){var _43=B(_3W(_3Y.b));return new T2(0,_43.a,_43.b);});return (_3J+E(_40.a)*E(_40.b)<=Math.sqrt(Math.pow(_3R-E(_41.a),2)+Math.pow(_3T-E(_41.b),2)))?new T2(0,new T(function(){return E(E(_42).a);}),new T2(1,_3Z,new T(function(){return E(E(_42).b);}))):new T2(0,new T2(1,_3Z,new T(function(){return E(E(_42).a);})),new T(function(){return E(E(_42).b);}));}},_44=B(_3W(_3A.b));return new T2(0,_44.a,_44.b);});if(_3J+_3N*_3O<=Math.sqrt(Math.pow(_3R-_3S,2)+Math.pow(_3T-_3U,2))){var _45=E(_3V),_46=_45.b,_47=E(_45.a);if(!_47._){return new T2(0,_3B,new T2(1,_3K,_46));}else{var _48=_47.a,_49=new T(function(){var _4a=E(_3C),_4b=E(E(_48).b);return new T2(0,new T(function(){return E(_4a.a)+ -E(_4b.a);}),new T(function(){return E(_4a.b)+ -E(_4b.b);}));}),_4c=new T(function(){var _4d=E(E(_48).b),_4e=E(_3C);return new T2(0,new T(function(){return E(_4d.a)+ -E(_4e.a);}),new T(function(){return E(_4d.b)+ -E(_4e.b);}));}),_4f=new T(function(){var _4g=E(_48),_4h=new T(function(){var _4i=E(_4g.c);return new T5(0,_4i.a,_4i.b,_4i.c,new T(function(){return E(_4i.d)+1|0;}),_4i.e);}),_4j=new T(function(){var _4k=E(_4g.b),_4l=E(_4c);return new T2(0,new T(function(){return E(_4k.a)+ -E(_4l.a);}),new T(function(){return E(_4k.b)+ -E(_4l.b);}));}),_4m=new T(function(){var _4n=E(_4g.a),_4o=E(_4c);return new T2(0,new T(function(){return E(_4n.a)+ -E(_4o.a);}),new T(function(){return E(_4n.b)+ -E(_4o.b);}));});return new T3(0,_4m,_4j,_4h);}),_4p=new T(function(){var _4q=E(_3C),_4r=E(_49);return new T2(0,new T(function(){return E(_4q.a)+ -E(_4r.a);}),new T(function(){return E(_4q.b)+ -E(_4r.b);}));}),_4s=new T(function(){var _4t=E(_49);return new T2(0,new T(function(){return _3R+ -E(_4t.a);}),new T(function(){return _3T+ -E(_4t.b);}));});return new T2(0,new T3(0,_4s,_4p,new T5(0,_3H,_3I,_3E,new T(function(){return E(_3F)+1|0;}),_3G)),new T2(1,_4f,new T(function(){return B(_R(_47.b,new T2(1,_3K,_46)));})));}}else{var _4u=new T(function(){var _4v=E(_3C),_4w=E(_3L);return new T2(0,new T(function(){return E(_4v.a)+ -E(_4w.a);}),new T(function(){return E(_4v.b)+ -E(_4w.b);}));}),_4x=new T(function(){var _4y=E(_3L),_4z=E(_3C);return new T2(0,new T(function(){return E(_4y.a)+ -E(_4z.a);}),new T(function(){return E(_4y.b)+ -E(_4z.b);}));}),_4A=new T(function(){var _4B=E(_3L),_4C=E(_4x);return new T2(0,new T(function(){return E(_4B.a)+ -E(_4C.a);}),new T(function(){return E(_4B.b)+ -E(_4C.b);}));}),_4D=new T(function(){var _4E=E(_4x);return new T2(0,new T(function(){return _3S+ -E(_4E.a);}),new T(function(){return _3U+ -E(_4E.b);}));}),_4F=new T(function(){var _4G=E(_3C),_4H=E(_4u);return new T2(0,new T(function(){return E(_4G.a)+ -E(_4H.a);}),new T(function(){return E(_4G.b)+ -E(_4H.b);}));}),_4I=new T(function(){var _4J=E(_4u);return new T2(0,new T(function(){return _3R+ -E(_4J.a);}),new T(function(){return _3T+ -E(_4J.b);}));});return new T2(0,new T3(0,_4I,_4F,new T5(0,_3H,_3I,_3E,new T(function(){return E(_3F)+1|0;}),_3G)),new T2(1,new T3(0,_4D,_4A,new T5(0,_3N,_3O,_3M.c,new T(function(){return E(_3M.d)+1|0;}),_3M.e)),new T(function(){var _4K=E(_3V);return B(_R(_4K.a,_4K.b));})));}}});return new T2(1,new T(function(){return E(E(_3z).a);}),new T(function(){return B(_3v(E(_3z).b));}));}},_4L=",",_4M="rgba(",_4N=new T(function(){return toJSStr(_v);}),_4O="rgb(",_4P=")",_4Q=new T2(1,_4P,_v),_4R=function(_4S){var _4T=E(_4S);if(!_4T._){var _4U=jsCat(new T2(1,_4O,new T2(1,new T(function(){return String(_4T.a);}),new T2(1,_4L,new T2(1,new T(function(){return String(_4T.b);}),new T2(1,_4L,new T2(1,new T(function(){return String(_4T.c);}),_4Q)))))),E(_4N));return E(_4U);}else{var _4V=jsCat(new T2(1,_4M,new T2(1,new T(function(){return String(_4T.a);}),new T2(1,_4L,new T2(1,new T(function(){return String(_4T.b);}),new T2(1,_4L,new T2(1,new T(function(){return String(_4T.c);}),new T2(1,_4L,new T2(1,new T(function(){return String(_4T.d);}),_4Q)))))))),E(_4N));return E(_4V);}},_4W="strokeStyle",_4X="fillStyle",_4Y=new T(function(){return eval("(function(e,p){return e[p].toString();})");}),_4Z=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_50=function(_51,_52){var _53=new T(function(){return B(_4R(_51));});return function(_54,_){var _55=E(_54),_56=E(_4X),_57=E(_4Y),_58=__app2(_57,_55,_56),_59=E(_4W),_5a=__app2(_57,_55,_59),_5b=E(_53),_5c=E(_4Z),_5d=__app3(_5c,_55,_56,_5b),_5e=__app3(_5c,_55,_59,_5b),_5f=B(A2(_52,_55,_)),_5g=String(_58),_5h=__app3(_5c,_55,_56,_5g),_5i=String(_5a),_5j=__app3(_5c,_55,_59,_5i);return new F(function(){return _2R(_);});};},_5k=new T3(0,0,255,0),_5l=new T3(0,255,0,0),_5m=new T3(0,0,0,0),_5n=new T1(0,16),_5o=function(_5p){var _5q=E(_5p),_5r=E(_5q.a);return new T2(0,Math.sqrt(Math.pow( -E(_5r.a),2)+Math.pow( -E(_5r.b),2)),_5q);},_5s=function(_5t,_5u){var _5v=E(E(_5t).a),_5w=E(E(_5u).a);return (_5v>=_5w)?(_5v!=_5w)?2:1:0;},_5x=function(_5y,_){var _5z=__app1(E(_1),_5y);if(!_5z){return _2d;}else{var _5A=__app1(E(_0),_5y);return new T1(1,new T2(0,_5A,_5y));}},_5B=function(_5C,_){return new F(function(){return _5x(E(_5C),_);});},_5D=function(_5E){return E(_5E).b;},_5F=new T2(0,_5D,_5B),_5G=function(_5H){return E(E(_5H).a);},_5I=function(_5J){return E(E(_5J).b);},_5K=function(_5L){return new F(function(){return fromJSStr(E(_5L));});},_5M=function(_5N){return E(E(_5N).a);},_5O=function(_5P,_5Q,_5R,_5S){var _5T=new T(function(){var _5U=function(_){var _5V=__app2(E(_4Y),B(A2(_5M,_5P,_5R)),E(_5S));return new T(function(){return String(_5V);});};return E(_5U);});return new F(function(){return A2(_2D,_5Q,_5T);});},_5W=function(_5X){return E(E(_5X).d);},_5Y=function(_5Z,_60,_61,_62){var _63=B(_5G(_60)),_64=new T(function(){return B(_5W(_63));}),_65=function(_66){return new F(function(){return A1(_64,new T(function(){return B(_5K(_66));}));});},_67=new T(function(){return B(_5O(_5Z,_60,_61,new T(function(){return toJSStr(E(_62));},1)));});return new F(function(){return A3(_5I,_63,_67,_65);});},_68=new T(function(){return B(unCStr("width"));}),_69=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_6a=new T(function(){return B(err(_69));}),_6b=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_6c=new T(function(){return B(err(_6b));}),_6d=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6e=new T(function(){return B(unCStr("base"));}),_6f=new T(function(){return B(unCStr("PatternMatchFail"));}),_6g=new T(function(){var _6h=hs_wordToWord64(new Long(18445595,3739165398,true)),_6i=hs_wordToWord64(new Long(52003073,3246954884,true));return new T5(0,_6h,_6i,new T5(0,_6h,_6i,_6e,_6d,_6f),_v,_v);}),_6j=function(_6k){return E(_6g);},_6l=function(_6m){var _6n=E(_6m);return new F(function(){return _D(B(_B(_6n.a)),_6j,_6n.b);});},_6o=function(_6p){return E(E(_6p).a);},_6q=function(_6r){return new T2(0,_6s,_6r);},_6t=function(_6u,_6v){return new F(function(){return _R(E(_6u).a,_6v);});},_6w=function(_6x,_6y){return new F(function(){return _1V(_6t,_6x,_6y);});},_6z=function(_6A,_6B,_6C){return new F(function(){return _R(E(_6B).a,_6C);});},_6D=new T3(0,_6z,_6o,_6w),_6s=new T(function(){return new T5(0,_6j,_6D,_6q,_6l,_6o);}),_6E=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6F=function(_6G,_6H){return new F(function(){return die(new T(function(){return B(A2(_2b,_6H,_6G));}));});},_6I=function(_6J,_6K){return new F(function(){return _6F(_6J,_6K);});},_6L=function(_6M,_6N){var _6O=E(_6N);if(!_6O._){return new T2(0,_v,_v);}else{var _6P=_6O.a;if(!B(A1(_6M,_6P))){return new T2(0,_v,_6O);}else{var _6Q=new T(function(){var _6R=B(_6L(_6M,_6O.b));return new T2(0,_6R.a,_6R.b);});return new T2(0,new T2(1,_6P,new T(function(){return E(E(_6Q).a);})),new T(function(){return E(E(_6Q).b);}));}}},_6S=32,_6T=new T(function(){return B(unCStr("\n"));}),_6U=function(_6V){return (E(_6V)==124)?false:true;},_6W=function(_6X,_6Y){var _6Z=B(_6L(_6U,B(unCStr(_6X)))),_70=_6Z.a,_71=function(_72,_73){var _74=new T(function(){var _75=new T(function(){return B(_R(_6Y,new T(function(){return B(_R(_73,_6T));},1)));});return B(unAppCStr(": ",_75));},1);return new F(function(){return _R(_72,_74);});},_76=E(_6Z.b);if(!_76._){return new F(function(){return _71(_70,_v);});}else{if(E(_76.a)==124){return new F(function(){return _71(_70,new T2(1,_6S,_76.b));});}else{return new F(function(){return _71(_70,_v);});}}},_77=function(_78){return new F(function(){return _6I(new T1(0,new T(function(){return B(_6W(_78,_6E));})),_6s);});},_79=new T(function(){return B(_77("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7a=function(_7b,_7c){while(1){var _7d=B((function(_7e,_7f){var _7g=E(_7e);switch(_7g._){case 0:var _7h=E(_7f);if(!_7h._){return __Z;}else{_7b=B(A1(_7g.a,_7h.a));_7c=_7h.b;return __continue;}break;case 1:var _7i=B(A1(_7g.a,_7f)),_7j=_7f;_7b=_7i;_7c=_7j;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_7g.a,_7f),new T(function(){return B(_7a(_7g.b,_7f));}));default:return E(_7g.a);}})(_7b,_7c));if(_7d!=__continue){return _7d;}}},_7k=function(_7l,_7m){var _7n=function(_7o){var _7p=E(_7m);if(_7p._==3){return new T2(3,_7p.a,new T(function(){return B(_7k(_7l,_7p.b));}));}else{var _7q=E(_7l);if(_7q._==2){return E(_7p);}else{var _7r=E(_7p);if(_7r._==2){return E(_7q);}else{var _7s=function(_7t){var _7u=E(_7r);if(_7u._==4){var _7v=function(_7w){return new T1(4,new T(function(){return B(_R(B(_7a(_7q,_7w)),_7u.a));}));};return new T1(1,_7v);}else{var _7x=E(_7q);if(_7x._==1){var _7y=_7x.a,_7z=E(_7u);if(!_7z._){return new T1(1,function(_7A){return new F(function(){return _7k(B(A1(_7y,_7A)),_7z);});});}else{var _7B=function(_7C){return new F(function(){return _7k(B(A1(_7y,_7C)),new T(function(){return B(A1(_7z.a,_7C));}));});};return new T1(1,_7B);}}else{var _7D=E(_7u);if(!_7D._){return E(_79);}else{var _7E=function(_7F){return new F(function(){return _7k(_7x,new T(function(){return B(A1(_7D.a,_7F));}));});};return new T1(1,_7E);}}}},_7G=E(_7q);switch(_7G._){case 1:var _7H=E(_7r);if(_7H._==4){var _7I=function(_7J){return new T1(4,new T(function(){return B(_R(B(_7a(B(A1(_7G.a,_7J)),_7J)),_7H.a));}));};return new T1(1,_7I);}else{return new F(function(){return _7s(_);});}break;case 4:var _7K=_7G.a,_7L=E(_7r);switch(_7L._){case 0:var _7M=function(_7N){var _7O=new T(function(){return B(_R(_7K,new T(function(){return B(_7a(_7L,_7N));},1)));});return new T1(4,_7O);};return new T1(1,_7M);case 1:var _7P=function(_7Q){var _7R=new T(function(){return B(_R(_7K,new T(function(){return B(_7a(B(A1(_7L.a,_7Q)),_7Q));},1)));});return new T1(4,_7R);};return new T1(1,_7P);default:return new T1(4,new T(function(){return B(_R(_7K,_7L.a));}));}break;default:return new F(function(){return _7s(_);});}}}}},_7S=E(_7l);switch(_7S._){case 0:var _7T=E(_7m);if(!_7T._){var _7U=function(_7V){return new F(function(){return _7k(B(A1(_7S.a,_7V)),new T(function(){return B(A1(_7T.a,_7V));}));});};return new T1(0,_7U);}else{return new F(function(){return _7n(_);});}break;case 3:return new T2(3,_7S.a,new T(function(){return B(_7k(_7S.b,_7m));}));default:return new F(function(){return _7n(_);});}},_7W=new T(function(){return B(unCStr("("));}),_7X=new T(function(){return B(unCStr(")"));}),_7Y=function(_7Z,_80){while(1){var _81=E(_7Z);if(!_81._){return (E(_80)._==0)?true:false;}else{var _82=E(_80);if(!_82._){return false;}else{if(E(_81.a)!=E(_82.a)){return false;}else{_7Z=_81.b;_80=_82.b;continue;}}}}},_83=function(_84,_85){return E(_84)!=E(_85);},_86=function(_87,_88){return E(_87)==E(_88);},_89=new T2(0,_86,_83),_8a=function(_8b,_8c){while(1){var _8d=E(_8b);if(!_8d._){return (E(_8c)._==0)?true:false;}else{var _8e=E(_8c);if(!_8e._){return false;}else{if(E(_8d.a)!=E(_8e.a)){return false;}else{_8b=_8d.b;_8c=_8e.b;continue;}}}}},_8f=function(_8g,_8h){return (!B(_8a(_8g,_8h)))?true:false;},_8i=new T2(0,_8a,_8f),_8j=function(_8k,_8l){var _8m=E(_8k);switch(_8m._){case 0:return new T1(0,function(_8n){return new F(function(){return _8j(B(A1(_8m.a,_8n)),_8l);});});case 1:return new T1(1,function(_8o){return new F(function(){return _8j(B(A1(_8m.a,_8o)),_8l);});});case 2:return new T0(2);case 3:return new F(function(){return _7k(B(A1(_8l,_8m.a)),new T(function(){return B(_8j(_8m.b,_8l));}));});break;default:var _8p=function(_8q){var _8r=E(_8q);if(!_8r._){return __Z;}else{var _8s=E(_8r.a);return new F(function(){return _R(B(_7a(B(A1(_8l,_8s.a)),_8s.b)),new T(function(){return B(_8p(_8r.b));},1));});}},_8t=B(_8p(_8m.a));return (_8t._==0)?new T0(2):new T1(4,_8t);}},_8u=new T0(2),_8v=function(_8w){return new T2(3,_8w,_8u);},_8x=function(_8y,_8z){var _8A=E(_8y);if(!_8A){return new F(function(){return A1(_8z,_2Q);});}else{var _8B=new T(function(){return B(_8x(_8A-1|0,_8z));});return new T1(0,function(_8C){return E(_8B);});}},_8D=function(_8E,_8F,_8G){var _8H=new T(function(){return B(A1(_8E,_8v));}),_8I=function(_8J,_8K,_8L,_8M){while(1){var _8N=B((function(_8O,_8P,_8Q,_8R){var _8S=E(_8O);switch(_8S._){case 0:var _8T=E(_8P);if(!_8T._){return new F(function(){return A1(_8F,_8R);});}else{var _8U=_8Q+1|0,_8V=_8R;_8J=B(A1(_8S.a,_8T.a));_8K=_8T.b;_8L=_8U;_8M=_8V;return __continue;}break;case 1:var _8W=B(A1(_8S.a,_8P)),_8X=_8P,_8U=_8Q,_8V=_8R;_8J=_8W;_8K=_8X;_8L=_8U;_8M=_8V;return __continue;case 2:return new F(function(){return A1(_8F,_8R);});break;case 3:var _8Y=new T(function(){return B(_8j(_8S,_8R));});return new F(function(){return _8x(_8Q,function(_8Z){return E(_8Y);});});break;default:return new F(function(){return _8j(_8S,_8R);});}})(_8J,_8K,_8L,_8M));if(_8N!=__continue){return _8N;}}};return function(_90){return new F(function(){return _8I(_8H,_90,0,_8G);});};},_91=function(_92){return new F(function(){return A1(_92,_v);});},_93=function(_94,_95){var _96=function(_97){var _98=E(_97);if(!_98._){return E(_91);}else{var _99=_98.a;if(!B(A1(_94,_99))){return E(_91);}else{var _9a=new T(function(){return B(_96(_98.b));}),_9b=function(_9c){var _9d=new T(function(){return B(A1(_9a,function(_9e){return new F(function(){return A1(_9c,new T2(1,_99,_9e));});}));});return new T1(0,function(_9f){return E(_9d);});};return E(_9b);}}};return function(_9g){return new F(function(){return A2(_96,_9g,_95);});};},_9h=new T0(6),_9i=new T(function(){return B(unCStr("valDig: Bad base"));}),_9j=new T(function(){return B(err(_9i));}),_9k=function(_9l,_9m){var _9n=function(_9o,_9p){var _9q=E(_9o);if(!_9q._){var _9r=new T(function(){return B(A1(_9p,_v));});return function(_9s){return new F(function(){return A1(_9s,_9r);});};}else{var _9t=E(_9q.a),_9u=function(_9v){var _9w=new T(function(){return B(_9n(_9q.b,function(_9x){return new F(function(){return A1(_9p,new T2(1,_9v,_9x));});}));}),_9y=function(_9z){var _9A=new T(function(){return B(A1(_9w,_9z));});return new T1(0,function(_9B){return E(_9A);});};return E(_9y);};switch(E(_9l)){case 8:if(48>_9t){var _9C=new T(function(){return B(A1(_9p,_v));});return function(_9D){return new F(function(){return A1(_9D,_9C);});};}else{if(_9t>55){var _9E=new T(function(){return B(A1(_9p,_v));});return function(_9F){return new F(function(){return A1(_9F,_9E);});};}else{return new F(function(){return _9u(_9t-48|0);});}}break;case 10:if(48>_9t){var _9G=new T(function(){return B(A1(_9p,_v));});return function(_9H){return new F(function(){return A1(_9H,_9G);});};}else{if(_9t>57){var _9I=new T(function(){return B(A1(_9p,_v));});return function(_9J){return new F(function(){return A1(_9J,_9I);});};}else{return new F(function(){return _9u(_9t-48|0);});}}break;case 16:if(48>_9t){if(97>_9t){if(65>_9t){var _9K=new T(function(){return B(A1(_9p,_v));});return function(_9L){return new F(function(){return A1(_9L,_9K);});};}else{if(_9t>70){var _9M=new T(function(){return B(A1(_9p,_v));});return function(_9N){return new F(function(){return A1(_9N,_9M);});};}else{return new F(function(){return _9u((_9t-65|0)+10|0);});}}}else{if(_9t>102){if(65>_9t){var _9O=new T(function(){return B(A1(_9p,_v));});return function(_9P){return new F(function(){return A1(_9P,_9O);});};}else{if(_9t>70){var _9Q=new T(function(){return B(A1(_9p,_v));});return function(_9R){return new F(function(){return A1(_9R,_9Q);});};}else{return new F(function(){return _9u((_9t-65|0)+10|0);});}}}else{return new F(function(){return _9u((_9t-97|0)+10|0);});}}}else{if(_9t>57){if(97>_9t){if(65>_9t){var _9S=new T(function(){return B(A1(_9p,_v));});return function(_9T){return new F(function(){return A1(_9T,_9S);});};}else{if(_9t>70){var _9U=new T(function(){return B(A1(_9p,_v));});return function(_9V){return new F(function(){return A1(_9V,_9U);});};}else{return new F(function(){return _9u((_9t-65|0)+10|0);});}}}else{if(_9t>102){if(65>_9t){var _9W=new T(function(){return B(A1(_9p,_v));});return function(_9X){return new F(function(){return A1(_9X,_9W);});};}else{if(_9t>70){var _9Y=new T(function(){return B(A1(_9p,_v));});return function(_9Z){return new F(function(){return A1(_9Z,_9Y);});};}else{return new F(function(){return _9u((_9t-65|0)+10|0);});}}}else{return new F(function(){return _9u((_9t-97|0)+10|0);});}}}else{return new F(function(){return _9u(_9t-48|0);});}}break;default:return E(_9j);}}},_a0=function(_a1){var _a2=E(_a1);if(!_a2._){return new T0(2);}else{return new F(function(){return A1(_9m,_a2);});}};return function(_a3){return new F(function(){return A3(_9n,_a3,_2t,_a0);});};},_a4=16,_a5=8,_a6=function(_a7){var _a8=function(_a9){return new F(function(){return A1(_a7,new T1(5,new T2(0,_a5,_a9)));});},_aa=function(_ab){return new F(function(){return A1(_a7,new T1(5,new T2(0,_a4,_ab)));});},_ac=function(_ad){switch(E(_ad)){case 79:return new T1(1,B(_9k(_a5,_a8)));case 88:return new T1(1,B(_9k(_a4,_aa)));case 111:return new T1(1,B(_9k(_a5,_a8)));case 120:return new T1(1,B(_9k(_a4,_aa)));default:return new T0(2);}};return function(_ae){return (E(_ae)==48)?E(new T1(0,_ac)):new T0(2);};},_af=function(_ag){return new T1(0,B(_a6(_ag)));},_ah=function(_ai){return new F(function(){return A1(_ai,_2d);});},_aj=function(_ak){return new F(function(){return A1(_ak,_2d);});},_al=10,_am=new T1(0,1),_an=new T1(0,2147483647),_ao=function(_ap,_aq){while(1){var _ar=E(_ap);if(!_ar._){var _as=_ar.a,_at=E(_aq);if(!_at._){var _au=_at.a,_av=addC(_as,_au);if(!E(_av.b)){return new T1(0,_av.a);}else{_ap=new T1(1,I_fromInt(_as));_aq=new T1(1,I_fromInt(_au));continue;}}else{_ap=new T1(1,I_fromInt(_as));_aq=_at;continue;}}else{var _aw=E(_aq);if(!_aw._){_ap=_ar;_aq=new T1(1,I_fromInt(_aw.a));continue;}else{return new T1(1,I_add(_ar.a,_aw.a));}}}},_ax=new T(function(){return B(_ao(_an,_am));}),_ay=function(_az){var _aA=E(_az);if(!_aA._){var _aB=E(_aA.a);return (_aB==(-2147483648))?E(_ax):new T1(0, -_aB);}else{return new T1(1,I_negate(_aA.a));}},_aC=new T1(0,10),_aD=function(_aE,_aF){while(1){var _aG=E(_aE);if(!_aG._){return E(_aF);}else{var _aH=_aF+1|0;_aE=_aG.b;_aF=_aH;continue;}}},_aI=function(_aJ,_aK){var _aL=E(_aK);return (_aL._==0)?__Z:new T2(1,new T(function(){return B(A1(_aJ,_aL.a));}),new T(function(){return B(_aI(_aJ,_aL.b));}));},_aM=function(_aN){return new T1(0,_aN);},_aO=function(_aP){return new F(function(){return _aM(E(_aP));});},_aQ=new T(function(){return B(unCStr("this should not happen"));}),_aR=new T(function(){return B(err(_aQ));}),_aS=function(_aT,_aU){while(1){var _aV=E(_aT);if(!_aV._){var _aW=_aV.a,_aX=E(_aU);if(!_aX._){var _aY=_aX.a;if(!(imul(_aW,_aY)|0)){return new T1(0,imul(_aW,_aY)|0);}else{_aT=new T1(1,I_fromInt(_aW));_aU=new T1(1,I_fromInt(_aY));continue;}}else{_aT=new T1(1,I_fromInt(_aW));_aU=_aX;continue;}}else{var _aZ=E(_aU);if(!_aZ._){_aT=_aV;_aU=new T1(1,I_fromInt(_aZ.a));continue;}else{return new T1(1,I_mul(_aV.a,_aZ.a));}}}},_b0=function(_b1,_b2){var _b3=E(_b2);if(!_b3._){return __Z;}else{var _b4=E(_b3.b);return (_b4._==0)?E(_aR):new T2(1,B(_ao(B(_aS(_b3.a,_b1)),_b4.a)),new T(function(){return B(_b0(_b1,_b4.b));}));}},_b5=new T1(0,0),_b6=function(_b7,_b8,_b9){while(1){var _ba=B((function(_bb,_bc,_bd){var _be=E(_bd);if(!_be._){return E(_b5);}else{if(!E(_be.b)._){return E(_be.a);}else{var _bf=E(_bc);if(_bf<=40){var _bg=function(_bh,_bi){while(1){var _bj=E(_bi);if(!_bj._){return E(_bh);}else{var _bk=B(_ao(B(_aS(_bh,_bb)),_bj.a));_bh=_bk;_bi=_bj.b;continue;}}};return new F(function(){return _bg(_b5,_be);});}else{var _bl=B(_aS(_bb,_bb));if(!(_bf%2)){var _bm=B(_b0(_bb,_be));_b7=_bl;_b8=quot(_bf+1|0,2);_b9=_bm;return __continue;}else{var _bm=B(_b0(_bb,new T2(1,_b5,_be)));_b7=_bl;_b8=quot(_bf+1|0,2);_b9=_bm;return __continue;}}}}})(_b7,_b8,_b9));if(_ba!=__continue){return _ba;}}},_bn=function(_bo,_bp){return new F(function(){return _b6(_bo,new T(function(){return B(_aD(_bp,0));},1),B(_aI(_aO,_bp)));});},_bq=function(_br){var _bs=new T(function(){var _bt=new T(function(){var _bu=function(_bv){return new F(function(){return A1(_br,new T1(1,new T(function(){return B(_bn(_aC,_bv));})));});};return new T1(1,B(_9k(_al,_bu)));}),_bw=function(_bx){if(E(_bx)==43){var _by=function(_bz){return new F(function(){return A1(_br,new T1(1,new T(function(){return B(_bn(_aC,_bz));})));});};return new T1(1,B(_9k(_al,_by)));}else{return new T0(2);}},_bA=function(_bB){if(E(_bB)==45){var _bC=function(_bD){return new F(function(){return A1(_br,new T1(1,new T(function(){return B(_ay(B(_bn(_aC,_bD))));})));});};return new T1(1,B(_9k(_al,_bC)));}else{return new T0(2);}};return B(_7k(B(_7k(new T1(0,_bA),new T1(0,_bw))),_bt));});return new F(function(){return _7k(new T1(0,function(_bE){return (E(_bE)==101)?E(_bs):new T0(2);}),new T1(0,function(_bF){return (E(_bF)==69)?E(_bs):new T0(2);}));});},_bG=function(_bH){var _bI=function(_bJ){return new F(function(){return A1(_bH,new T1(1,_bJ));});};return function(_bK){return (E(_bK)==46)?new T1(1,B(_9k(_al,_bI))):new T0(2);};},_bL=function(_bM){return new T1(0,B(_bG(_bM)));},_bN=function(_bO){var _bP=function(_bQ){var _bR=function(_bS){return new T1(1,B(_8D(_bq,_ah,function(_bT){return new F(function(){return A1(_bO,new T1(5,new T3(1,_bQ,_bS,_bT)));});})));};return new T1(1,B(_8D(_bL,_aj,_bR)));};return new F(function(){return _9k(_al,_bP);});},_bU=function(_bV){return new T1(1,B(_bN(_bV)));},_bW=function(_bX){return E(E(_bX).a);},_bY=function(_bZ,_c0,_c1){while(1){var _c2=E(_c1);if(!_c2._){return false;}else{if(!B(A3(_bW,_bZ,_c0,_c2.a))){_c1=_c2.b;continue;}else{return true;}}}},_c3=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_c4=function(_c5){return new F(function(){return _bY(_89,_c5,_c3);});},_c6=false,_c7=true,_c8=function(_c9){var _ca=new T(function(){return B(A1(_c9,_a5));}),_cb=new T(function(){return B(A1(_c9,_a4));});return function(_cc){switch(E(_cc)){case 79:return E(_ca);case 88:return E(_cb);case 111:return E(_ca);case 120:return E(_cb);default:return new T0(2);}};},_cd=function(_ce){return new T1(0,B(_c8(_ce)));},_cf=function(_cg){return new F(function(){return A1(_cg,_al);});},_ch=function(_ci){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_3h(9,_ci,_v));}))));});},_cj=function(_ck){var _cl=E(_ck);if(!_cl._){return E(_cl.a);}else{return new F(function(){return I_toInt(_cl.a);});}},_cm=function(_cn,_co){var _cp=E(_cn);if(!_cp._){var _cq=_cp.a,_cr=E(_co);return (_cr._==0)?_cq<=_cr.a:I_compareInt(_cr.a,_cq)>=0;}else{var _cs=_cp.a,_ct=E(_co);return (_ct._==0)?I_compareInt(_cs,_ct.a)<=0:I_compare(_cs,_ct.a)<=0;}},_cu=function(_cv){return new T0(2);},_cw=function(_cx){var _cy=E(_cx);if(!_cy._){return E(_cu);}else{var _cz=_cy.a,_cA=E(_cy.b);if(!_cA._){return E(_cz);}else{var _cB=new T(function(){return B(_cw(_cA));}),_cC=function(_cD){return new F(function(){return _7k(B(A1(_cz,_cD)),new T(function(){return B(A1(_cB,_cD));}));});};return E(_cC);}}},_cE=function(_cF,_cG){var _cH=function(_cI,_cJ,_cK){var _cL=E(_cI);if(!_cL._){return new F(function(){return A1(_cK,_cF);});}else{var _cM=E(_cJ);if(!_cM._){return new T0(2);}else{if(E(_cL.a)!=E(_cM.a)){return new T0(2);}else{var _cN=new T(function(){return B(_cH(_cL.b,_cM.b,_cK));});return new T1(0,function(_cO){return E(_cN);});}}}};return function(_cP){return new F(function(){return _cH(_cF,_cP,_cG);});};},_cQ=new T(function(){return B(unCStr("SO"));}),_cR=14,_cS=function(_cT){var _cU=new T(function(){return B(A1(_cT,_cR));});return new T1(1,B(_cE(_cQ,function(_cV){return E(_cU);})));},_cW=new T(function(){return B(unCStr("SOH"));}),_cX=1,_cY=function(_cZ){var _d0=new T(function(){return B(A1(_cZ,_cX));});return new T1(1,B(_cE(_cW,function(_d1){return E(_d0);})));},_d2=function(_d3){return new T1(1,B(_8D(_cY,_cS,_d3)));},_d4=new T(function(){return B(unCStr("NUL"));}),_d5=0,_d6=function(_d7){var _d8=new T(function(){return B(A1(_d7,_d5));});return new T1(1,B(_cE(_d4,function(_d9){return E(_d8);})));},_da=new T(function(){return B(unCStr("STX"));}),_db=2,_dc=function(_dd){var _de=new T(function(){return B(A1(_dd,_db));});return new T1(1,B(_cE(_da,function(_df){return E(_de);})));},_dg=new T(function(){return B(unCStr("ETX"));}),_dh=3,_di=function(_dj){var _dk=new T(function(){return B(A1(_dj,_dh));});return new T1(1,B(_cE(_dg,function(_dl){return E(_dk);})));},_dm=new T(function(){return B(unCStr("EOT"));}),_dn=4,_do=function(_dp){var _dq=new T(function(){return B(A1(_dp,_dn));});return new T1(1,B(_cE(_dm,function(_dr){return E(_dq);})));},_ds=new T(function(){return B(unCStr("ENQ"));}),_dt=5,_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,_dt));});return new T1(1,B(_cE(_ds,function(_dx){return E(_dw);})));},_dy=new T(function(){return B(unCStr("ACK"));}),_dz=6,_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,_dz));});return new T1(1,B(_cE(_dy,function(_dD){return E(_dC);})));},_dE=new T(function(){return B(unCStr("BEL"));}),_dF=7,_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,_dF));});return new T1(1,B(_cE(_dE,function(_dJ){return E(_dI);})));},_dK=new T(function(){return B(unCStr("BS"));}),_dL=8,_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,_dL));});return new T1(1,B(_cE(_dK,function(_dP){return E(_dO);})));},_dQ=new T(function(){return B(unCStr("HT"));}),_dR=9,_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,_dR));});return new T1(1,B(_cE(_dQ,function(_dV){return E(_dU);})));},_dW=new T(function(){return B(unCStr("LF"));}),_dX=10,_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,_dX));});return new T1(1,B(_cE(_dW,function(_e1){return E(_e0);})));},_e2=new T(function(){return B(unCStr("VT"));}),_e3=11,_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,_e3));});return new T1(1,B(_cE(_e2,function(_e7){return E(_e6);})));},_e8=new T(function(){return B(unCStr("FF"));}),_e9=12,_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,_e9));});return new T1(1,B(_cE(_e8,function(_ed){return E(_ec);})));},_ee=new T(function(){return B(unCStr("CR"));}),_ef=13,_eg=function(_eh){var _ei=new T(function(){return B(A1(_eh,_ef));});return new T1(1,B(_cE(_ee,function(_ej){return E(_ei);})));},_ek=new T(function(){return B(unCStr("SI"));}),_el=15,_em=function(_en){var _eo=new T(function(){return B(A1(_en,_el));});return new T1(1,B(_cE(_ek,function(_ep){return E(_eo);})));},_eq=new T(function(){return B(unCStr("DLE"));}),_er=16,_es=function(_et){var _eu=new T(function(){return B(A1(_et,_er));});return new T1(1,B(_cE(_eq,function(_ev){return E(_eu);})));},_ew=new T(function(){return B(unCStr("DC1"));}),_ex=17,_ey=function(_ez){var _eA=new T(function(){return B(A1(_ez,_ex));});return new T1(1,B(_cE(_ew,function(_eB){return E(_eA);})));},_eC=new T(function(){return B(unCStr("DC2"));}),_eD=18,_eE=function(_eF){var _eG=new T(function(){return B(A1(_eF,_eD));});return new T1(1,B(_cE(_eC,function(_eH){return E(_eG);})));},_eI=new T(function(){return B(unCStr("DC3"));}),_eJ=19,_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,_eJ));});return new T1(1,B(_cE(_eI,function(_eN){return E(_eM);})));},_eO=new T(function(){return B(unCStr("DC4"));}),_eP=20,_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,_eP));});return new T1(1,B(_cE(_eO,function(_eT){return E(_eS);})));},_eU=new T(function(){return B(unCStr("NAK"));}),_eV=21,_eW=function(_eX){var _eY=new T(function(){return B(A1(_eX,_eV));});return new T1(1,B(_cE(_eU,function(_eZ){return E(_eY);})));},_f0=new T(function(){return B(unCStr("SYN"));}),_f1=22,_f2=function(_f3){var _f4=new T(function(){return B(A1(_f3,_f1));});return new T1(1,B(_cE(_f0,function(_f5){return E(_f4);})));},_f6=new T(function(){return B(unCStr("ETB"));}),_f7=23,_f8=function(_f9){var _fa=new T(function(){return B(A1(_f9,_f7));});return new T1(1,B(_cE(_f6,function(_fb){return E(_fa);})));},_fc=new T(function(){return B(unCStr("CAN"));}),_fd=24,_fe=function(_ff){var _fg=new T(function(){return B(A1(_ff,_fd));});return new T1(1,B(_cE(_fc,function(_fh){return E(_fg);})));},_fi=new T(function(){return B(unCStr("EM"));}),_fj=25,_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,_fj));});return new T1(1,B(_cE(_fi,function(_fn){return E(_fm);})));},_fo=new T(function(){return B(unCStr("SUB"));}),_fp=26,_fq=function(_fr){var _fs=new T(function(){return B(A1(_fr,_fp));});return new T1(1,B(_cE(_fo,function(_ft){return E(_fs);})));},_fu=new T(function(){return B(unCStr("ESC"));}),_fv=27,_fw=function(_fx){var _fy=new T(function(){return B(A1(_fx,_fv));});return new T1(1,B(_cE(_fu,function(_fz){return E(_fy);})));},_fA=new T(function(){return B(unCStr("FS"));}),_fB=28,_fC=function(_fD){var _fE=new T(function(){return B(A1(_fD,_fB));});return new T1(1,B(_cE(_fA,function(_fF){return E(_fE);})));},_fG=new T(function(){return B(unCStr("GS"));}),_fH=29,_fI=function(_fJ){var _fK=new T(function(){return B(A1(_fJ,_fH));});return new T1(1,B(_cE(_fG,function(_fL){return E(_fK);})));},_fM=new T(function(){return B(unCStr("RS"));}),_fN=30,_fO=function(_fP){var _fQ=new T(function(){return B(A1(_fP,_fN));});return new T1(1,B(_cE(_fM,function(_fR){return E(_fQ);})));},_fS=new T(function(){return B(unCStr("US"));}),_fT=31,_fU=function(_fV){var _fW=new T(function(){return B(A1(_fV,_fT));});return new T1(1,B(_cE(_fS,function(_fX){return E(_fW);})));},_fY=new T(function(){return B(unCStr("SP"));}),_fZ=32,_g0=function(_g1){var _g2=new T(function(){return B(A1(_g1,_fZ));});return new T1(1,B(_cE(_fY,function(_g3){return E(_g2);})));},_g4=new T(function(){return B(unCStr("DEL"));}),_g5=127,_g6=function(_g7){var _g8=new T(function(){return B(A1(_g7,_g5));});return new T1(1,B(_cE(_g4,function(_g9){return E(_g8);})));},_ga=new T2(1,_g6,_v),_gb=new T2(1,_g0,_ga),_gc=new T2(1,_fU,_gb),_gd=new T2(1,_fO,_gc),_ge=new T2(1,_fI,_gd),_gf=new T2(1,_fC,_ge),_gg=new T2(1,_fw,_gf),_gh=new T2(1,_fq,_gg),_gi=new T2(1,_fk,_gh),_gj=new T2(1,_fe,_gi),_gk=new T2(1,_f8,_gj),_gl=new T2(1,_f2,_gk),_gm=new T2(1,_eW,_gl),_gn=new T2(1,_eQ,_gm),_go=new T2(1,_eK,_gn),_gp=new T2(1,_eE,_go),_gq=new T2(1,_ey,_gp),_gr=new T2(1,_es,_gq),_gs=new T2(1,_em,_gr),_gt=new T2(1,_eg,_gs),_gu=new T2(1,_ea,_gt),_gv=new T2(1,_e4,_gu),_gw=new T2(1,_dY,_gv),_gx=new T2(1,_dS,_gw),_gy=new T2(1,_dM,_gx),_gz=new T2(1,_dG,_gy),_gA=new T2(1,_dA,_gz),_gB=new T2(1,_du,_gA),_gC=new T2(1,_do,_gB),_gD=new T2(1,_di,_gC),_gE=new T2(1,_dc,_gD),_gF=new T2(1,_d6,_gE),_gG=new T2(1,_d2,_gF),_gH=new T(function(){return B(_cw(_gG));}),_gI=34,_gJ=new T1(0,1114111),_gK=92,_gL=39,_gM=function(_gN){var _gO=new T(function(){return B(A1(_gN,_dF));}),_gP=new T(function(){return B(A1(_gN,_dL));}),_gQ=new T(function(){return B(A1(_gN,_dR));}),_gR=new T(function(){return B(A1(_gN,_dX));}),_gS=new T(function(){return B(A1(_gN,_e3));}),_gT=new T(function(){return B(A1(_gN,_e9));}),_gU=new T(function(){return B(A1(_gN,_ef));}),_gV=new T(function(){return B(A1(_gN,_gK));}),_gW=new T(function(){return B(A1(_gN,_gL));}),_gX=new T(function(){return B(A1(_gN,_gI));}),_gY=new T(function(){var _gZ=function(_h0){var _h1=new T(function(){return B(_aM(E(_h0)));}),_h2=function(_h3){var _h4=B(_bn(_h1,_h3));if(!B(_cm(_h4,_gJ))){return new T0(2);}else{return new F(function(){return A1(_gN,new T(function(){var _h5=B(_cj(_h4));if(_h5>>>0>1114111){return B(_ch(_h5));}else{return _h5;}}));});}};return new T1(1,B(_9k(_h0,_h2)));},_h6=new T(function(){var _h7=new T(function(){return B(A1(_gN,_fT));}),_h8=new T(function(){return B(A1(_gN,_fN));}),_h9=new T(function(){return B(A1(_gN,_fH));}),_ha=new T(function(){return B(A1(_gN,_fB));}),_hb=new T(function(){return B(A1(_gN,_fv));}),_hc=new T(function(){return B(A1(_gN,_fp));}),_hd=new T(function(){return B(A1(_gN,_fj));}),_he=new T(function(){return B(A1(_gN,_fd));}),_hf=new T(function(){return B(A1(_gN,_f7));}),_hg=new T(function(){return B(A1(_gN,_f1));}),_hh=new T(function(){return B(A1(_gN,_eV));}),_hi=new T(function(){return B(A1(_gN,_eP));}),_hj=new T(function(){return B(A1(_gN,_eJ));}),_hk=new T(function(){return B(A1(_gN,_eD));}),_hl=new T(function(){return B(A1(_gN,_ex));}),_hm=new T(function(){return B(A1(_gN,_er));}),_hn=new T(function(){return B(A1(_gN,_el));}),_ho=new T(function(){return B(A1(_gN,_cR));}),_hp=new T(function(){return B(A1(_gN,_dz));}),_hq=new T(function(){return B(A1(_gN,_dt));}),_hr=new T(function(){return B(A1(_gN,_dn));}),_hs=new T(function(){return B(A1(_gN,_dh));}),_ht=new T(function(){return B(A1(_gN,_db));}),_hu=new T(function(){return B(A1(_gN,_cX));}),_hv=new T(function(){return B(A1(_gN,_d5));}),_hw=function(_hx){switch(E(_hx)){case 64:return E(_hv);case 65:return E(_hu);case 66:return E(_ht);case 67:return E(_hs);case 68:return E(_hr);case 69:return E(_hq);case 70:return E(_hp);case 71:return E(_gO);case 72:return E(_gP);case 73:return E(_gQ);case 74:return E(_gR);case 75:return E(_gS);case 76:return E(_gT);case 77:return E(_gU);case 78:return E(_ho);case 79:return E(_hn);case 80:return E(_hm);case 81:return E(_hl);case 82:return E(_hk);case 83:return E(_hj);case 84:return E(_hi);case 85:return E(_hh);case 86:return E(_hg);case 87:return E(_hf);case 88:return E(_he);case 89:return E(_hd);case 90:return E(_hc);case 91:return E(_hb);case 92:return E(_ha);case 93:return E(_h9);case 94:return E(_h8);case 95:return E(_h7);default:return new T0(2);}};return B(_7k(new T1(0,function(_hy){return (E(_hy)==94)?E(new T1(0,_hw)):new T0(2);}),new T(function(){return B(A1(_gH,_gN));})));});return B(_7k(new T1(1,B(_8D(_cd,_cf,_gZ))),_h6));});return new F(function(){return _7k(new T1(0,function(_hz){switch(E(_hz)){case 34:return E(_gX);case 39:return E(_gW);case 92:return E(_gV);case 97:return E(_gO);case 98:return E(_gP);case 102:return E(_gT);case 110:return E(_gR);case 114:return E(_gU);case 116:return E(_gQ);case 118:return E(_gS);default:return new T0(2);}}),_gY);});},_hA=function(_hB){return new F(function(){return A1(_hB,_2Q);});},_hC=function(_hD){var _hE=E(_hD);if(!_hE._){return E(_hA);}else{var _hF=E(_hE.a),_hG=_hF>>>0,_hH=new T(function(){return B(_hC(_hE.b));});if(_hG>887){var _hI=u_iswspace(_hF);if(!E(_hI)){return E(_hA);}else{var _hJ=function(_hK){var _hL=new T(function(){return B(A1(_hH,_hK));});return new T1(0,function(_hM){return E(_hL);});};return E(_hJ);}}else{var _hN=E(_hG);if(_hN==32){var _hO=function(_hP){var _hQ=new T(function(){return B(A1(_hH,_hP));});return new T1(0,function(_hR){return E(_hQ);});};return E(_hO);}else{if(_hN-9>>>0>4){if(E(_hN)==160){var _hS=function(_hT){var _hU=new T(function(){return B(A1(_hH,_hT));});return new T1(0,function(_hV){return E(_hU);});};return E(_hS);}else{return E(_hA);}}else{var _hW=function(_hX){var _hY=new T(function(){return B(A1(_hH,_hX));});return new T1(0,function(_hZ){return E(_hY);});};return E(_hW);}}}}},_i0=function(_i1){var _i2=new T(function(){return B(_i0(_i1));}),_i3=function(_i4){return (E(_i4)==92)?E(_i2):new T0(2);},_i5=function(_i6){return E(new T1(0,_i3));},_i7=new T1(1,function(_i8){return new F(function(){return A2(_hC,_i8,_i5);});}),_i9=new T(function(){return B(_gM(function(_ia){return new F(function(){return A1(_i1,new T2(0,_ia,_c7));});}));}),_ib=function(_ic){var _id=E(_ic);if(_id==38){return E(_i2);}else{var _ie=_id>>>0;if(_ie>887){var _if=u_iswspace(_id);return (E(_if)==0)?new T0(2):E(_i7);}else{var _ig=E(_ie);return (_ig==32)?E(_i7):(_ig-9>>>0>4)?(E(_ig)==160)?E(_i7):new T0(2):E(_i7);}}};return new F(function(){return _7k(new T1(0,function(_ih){return (E(_ih)==92)?E(new T1(0,_ib)):new T0(2);}),new T1(0,function(_ii){var _ij=E(_ii);if(E(_ij)==92){return E(_i9);}else{return new F(function(){return A1(_i1,new T2(0,_ij,_c6));});}}));});},_ik=function(_il,_im){var _in=new T(function(){return B(A1(_im,new T1(1,new T(function(){return B(A1(_il,_v));}))));}),_io=function(_ip){var _iq=E(_ip),_ir=E(_iq.a);if(E(_ir)==34){if(!E(_iq.b)){return E(_in);}else{return new F(function(){return _ik(function(_is){return new F(function(){return A1(_il,new T2(1,_ir,_is));});},_im);});}}else{return new F(function(){return _ik(function(_it){return new F(function(){return A1(_il,new T2(1,_ir,_it));});},_im);});}};return new F(function(){return _i0(_io);});},_iu=new T(function(){return B(unCStr("_\'"));}),_iv=function(_iw){var _ix=u_iswalnum(_iw);if(!E(_ix)){return new F(function(){return _bY(_89,_iw,_iu);});}else{return true;}},_iy=function(_iz){return new F(function(){return _iv(E(_iz));});},_iA=new T(function(){return B(unCStr(",;()[]{}`"));}),_iB=new T(function(){return B(unCStr("=>"));}),_iC=new T2(1,_iB,_v),_iD=new T(function(){return B(unCStr("~"));}),_iE=new T2(1,_iD,_iC),_iF=new T(function(){return B(unCStr("@"));}),_iG=new T2(1,_iF,_iE),_iH=new T(function(){return B(unCStr("->"));}),_iI=new T2(1,_iH,_iG),_iJ=new T(function(){return B(unCStr("<-"));}),_iK=new T2(1,_iJ,_iI),_iL=new T(function(){return B(unCStr("|"));}),_iM=new T2(1,_iL,_iK),_iN=new T(function(){return B(unCStr("\\"));}),_iO=new T2(1,_iN,_iM),_iP=new T(function(){return B(unCStr("="));}),_iQ=new T2(1,_iP,_iO),_iR=new T(function(){return B(unCStr("::"));}),_iS=new T2(1,_iR,_iQ),_iT=new T(function(){return B(unCStr(".."));}),_iU=new T2(1,_iT,_iS),_iV=function(_iW){var _iX=new T(function(){return B(A1(_iW,_9h));}),_iY=new T(function(){var _iZ=new T(function(){var _j0=function(_j1){var _j2=new T(function(){return B(A1(_iW,new T1(0,_j1)));});return new T1(0,function(_j3){return (E(_j3)==39)?E(_j2):new T0(2);});};return B(_gM(_j0));}),_j4=function(_j5){var _j6=E(_j5);switch(E(_j6)){case 39:return new T0(2);case 92:return E(_iZ);default:var _j7=new T(function(){return B(A1(_iW,new T1(0,_j6)));});return new T1(0,function(_j8){return (E(_j8)==39)?E(_j7):new T0(2);});}},_j9=new T(function(){var _ja=new T(function(){return B(_ik(_2t,_iW));}),_jb=new T(function(){var _jc=new T(function(){var _jd=new T(function(){var _je=function(_jf){var _jg=E(_jf),_jh=u_iswalpha(_jg);return (E(_jh)==0)?(E(_jg)==95)?new T1(1,B(_93(_iy,function(_ji){return new F(function(){return A1(_iW,new T1(3,new T2(1,_jg,_ji)));});}))):new T0(2):new T1(1,B(_93(_iy,function(_jj){return new F(function(){return A1(_iW,new T1(3,new T2(1,_jg,_jj)));});})));};return B(_7k(new T1(0,_je),new T(function(){return new T1(1,B(_8D(_af,_bU,_iW)));})));}),_jk=function(_jl){return (!B(_bY(_89,_jl,_c3)))?new T0(2):new T1(1,B(_93(_c4,function(_jm){var _jn=new T2(1,_jl,_jm);if(!B(_bY(_8i,_jn,_iU))){return new F(function(){return A1(_iW,new T1(4,_jn));});}else{return new F(function(){return A1(_iW,new T1(2,_jn));});}})));};return B(_7k(new T1(0,_jk),_jd));});return B(_7k(new T1(0,function(_jo){if(!B(_bY(_89,_jo,_iA))){return new T0(2);}else{return new F(function(){return A1(_iW,new T1(2,new T2(1,_jo,_v)));});}}),_jc));});return B(_7k(new T1(0,function(_jp){return (E(_jp)==34)?E(_ja):new T0(2);}),_jb));});return B(_7k(new T1(0,function(_jq){return (E(_jq)==39)?E(new T1(0,_j4)):new T0(2);}),_j9));});return new F(function(){return _7k(new T1(1,function(_jr){return (E(_jr)._==0)?E(_iX):new T0(2);}),_iY);});},_js=0,_jt=function(_ju,_jv){var _jw=new T(function(){var _jx=new T(function(){var _jy=function(_jz){var _jA=new T(function(){var _jB=new T(function(){return B(A1(_jv,_jz));});return B(_iV(function(_jC){var _jD=E(_jC);return (_jD._==2)?(!B(_7Y(_jD.a,_7X)))?new T0(2):E(_jB):new T0(2);}));}),_jE=function(_jF){return E(_jA);};return new T1(1,function(_jG){return new F(function(){return A2(_hC,_jG,_jE);});});};return B(A2(_ju,_js,_jy));});return B(_iV(function(_jH){var _jI=E(_jH);return (_jI._==2)?(!B(_7Y(_jI.a,_7W)))?new T0(2):E(_jx):new T0(2);}));}),_jJ=function(_jK){return E(_jw);};return function(_jL){return new F(function(){return A2(_hC,_jL,_jJ);});};},_jM=function(_jN,_jO){var _jP=function(_jQ){var _jR=new T(function(){return B(A1(_jN,_jQ));}),_jS=function(_jT){return new F(function(){return _7k(B(A1(_jR,_jT)),new T(function(){return new T1(1,B(_jt(_jP,_jT)));}));});};return E(_jS);},_jU=new T(function(){return B(A1(_jN,_jO));}),_jV=function(_jW){return new F(function(){return _7k(B(A1(_jU,_jW)),new T(function(){return new T1(1,B(_jt(_jP,_jW)));}));});};return E(_jV);},_jX=function(_jY,_jZ){var _k0=function(_k1,_k2){var _k3=function(_k4){return new F(function(){return A1(_k2,new T(function(){return  -E(_k4);}));});},_k5=new T(function(){return B(_iV(function(_k6){return new F(function(){return A3(_jY,_k6,_k1,_k3);});}));}),_k7=function(_k8){return E(_k5);},_k9=function(_ka){return new F(function(){return A2(_hC,_ka,_k7);});},_kb=new T(function(){return B(_iV(function(_kc){var _kd=E(_kc);if(_kd._==4){var _ke=E(_kd.a);if(!_ke._){return new F(function(){return A3(_jY,_kd,_k1,_k2);});}else{if(E(_ke.a)==45){if(!E(_ke.b)._){return E(new T1(1,_k9));}else{return new F(function(){return A3(_jY,_kd,_k1,_k2);});}}else{return new F(function(){return A3(_jY,_kd,_k1,_k2);});}}}else{return new F(function(){return A3(_jY,_kd,_k1,_k2);});}}));}),_kf=function(_kg){return E(_kb);};return new T1(1,function(_kh){return new F(function(){return A2(_hC,_kh,_kf);});});};return new F(function(){return _jM(_k0,_jZ);});},_ki=new T(function(){return 1/0;}),_kj=function(_kk,_kl){return new F(function(){return A1(_kl,_ki);});},_km=new T(function(){return 0/0;}),_kn=function(_ko,_kp){return new F(function(){return A1(_kp,_km);});},_kq=new T(function(){return B(unCStr("NaN"));}),_kr=new T(function(){return B(unCStr("Infinity"));}),_ks=1024,_kt=-1021,_ku=new T(function(){return B(unCStr("GHC.Exception"));}),_kv=new T(function(){return B(unCStr("base"));}),_kw=new T(function(){return B(unCStr("ArithException"));}),_kx=new T(function(){var _ky=hs_wordToWord64(new Long(4194982440,719304104,true)),_kz=hs_wordToWord64(new Long(3110813675,1843557400,true));return new T5(0,_ky,_kz,new T5(0,_ky,_kz,_kv,_ku,_kw),_v,_v);}),_kA=function(_kB){return E(_kx);},_kC=function(_kD){var _kE=E(_kD);return new F(function(){return _D(B(_B(_kE.a)),_kA,_kE.b);});},_kF=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_kG=new T(function(){return B(unCStr("denormal"));}),_kH=new T(function(){return B(unCStr("divide by zero"));}),_kI=new T(function(){return B(unCStr("loss of precision"));}),_kJ=new T(function(){return B(unCStr("arithmetic underflow"));}),_kK=new T(function(){return B(unCStr("arithmetic overflow"));}),_kL=function(_kM,_kN){switch(E(_kM)){case 0:return new F(function(){return _R(_kK,_kN);});break;case 1:return new F(function(){return _R(_kJ,_kN);});break;case 2:return new F(function(){return _R(_kI,_kN);});break;case 3:return new F(function(){return _R(_kH,_kN);});break;case 4:return new F(function(){return _R(_kG,_kN);});break;default:return new F(function(){return _R(_kF,_kN);});}},_kO=function(_kP){return new F(function(){return _kL(_kP,_v);});},_kQ=function(_kR,_kS,_kT){return new F(function(){return _kL(_kS,_kT);});},_kU=function(_kV,_kW){return new F(function(){return _1V(_kL,_kV,_kW);});},_kX=new T3(0,_kQ,_kO,_kU),_kY=new T(function(){return new T5(0,_kA,_kX,_kZ,_kC,_kO);}),_kZ=function(_6K){return new T2(0,_kY,_6K);},_l0=3,_l1=new T(function(){return B(_kZ(_l0));}),_l2=new T(function(){return die(_l1);}),_l3=function(_l4,_l5){var _l6=E(_l4);if(!_l6._){var _l7=_l6.a,_l8=E(_l5);return (_l8._==0)?_l7==_l8.a:(I_compareInt(_l8.a,_l7)==0)?true:false;}else{var _l9=_l6.a,_la=E(_l5);return (_la._==0)?(I_compareInt(_l9,_la.a)==0)?true:false:(I_compare(_l9,_la.a)==0)?true:false;}},_lb=new T1(0,0),_lc=function(_ld,_le){while(1){var _lf=E(_ld);if(!_lf._){var _lg=E(_lf.a);if(_lg==(-2147483648)){_ld=new T1(1,I_fromInt(-2147483648));continue;}else{var _lh=E(_le);if(!_lh._){return new T1(0,_lg%_lh.a);}else{_ld=new T1(1,I_fromInt(_lg));_le=_lh;continue;}}}else{var _li=_lf.a,_lj=E(_le);return (_lj._==0)?new T1(1,I_rem(_li,I_fromInt(_lj.a))):new T1(1,I_rem(_li,_lj.a));}}},_lk=function(_ll,_lm){if(!B(_l3(_lm,_lb))){return new F(function(){return _lc(_ll,_lm);});}else{return E(_l2);}},_ln=function(_lo,_lp){while(1){if(!B(_l3(_lp,_lb))){var _lq=_lp,_lr=B(_lk(_lo,_lp));_lo=_lq;_lp=_lr;continue;}else{return E(_lo);}}},_ls=function(_lt){var _lu=E(_lt);if(!_lu._){var _lv=E(_lu.a);return (_lv==(-2147483648))?E(_ax):(_lv<0)?new T1(0, -_lv):E(_lu);}else{var _lw=_lu.a;return (I_compareInt(_lw,0)>=0)?E(_lu):new T1(1,I_negate(_lw));}},_lx=function(_ly,_lz){while(1){var _lA=E(_ly);if(!_lA._){var _lB=E(_lA.a);if(_lB==(-2147483648)){_ly=new T1(1,I_fromInt(-2147483648));continue;}else{var _lC=E(_lz);if(!_lC._){return new T1(0,quot(_lB,_lC.a));}else{_ly=new T1(1,I_fromInt(_lB));_lz=_lC;continue;}}}else{var _lD=_lA.a,_lE=E(_lz);return (_lE._==0)?new T1(0,I_toInt(I_quot(_lD,I_fromInt(_lE.a)))):new T1(1,I_quot(_lD,_lE.a));}}},_lF=5,_lG=new T(function(){return B(_kZ(_lF));}),_lH=new T(function(){return die(_lG);}),_lI=function(_lJ,_lK){if(!B(_l3(_lK,_lb))){var _lL=B(_ln(B(_ls(_lJ)),B(_ls(_lK))));return (!B(_l3(_lL,_lb)))?new T2(0,B(_lx(_lJ,_lL)),B(_lx(_lK,_lL))):E(_l2);}else{return E(_lH);}},_lM=new T1(0,1),_lN=new T(function(){return B(unCStr("Negative exponent"));}),_lO=new T(function(){return B(err(_lN));}),_lP=new T1(0,2),_lQ=new T(function(){return B(_l3(_lP,_lb));}),_lR=function(_lS,_lT){while(1){var _lU=E(_lS);if(!_lU._){var _lV=_lU.a,_lW=E(_lT);if(!_lW._){var _lX=_lW.a,_lY=subC(_lV,_lX);if(!E(_lY.b)){return new T1(0,_lY.a);}else{_lS=new T1(1,I_fromInt(_lV));_lT=new T1(1,I_fromInt(_lX));continue;}}else{_lS=new T1(1,I_fromInt(_lV));_lT=_lW;continue;}}else{var _lZ=E(_lT);if(!_lZ._){_lS=_lU;_lT=new T1(1,I_fromInt(_lZ.a));continue;}else{return new T1(1,I_sub(_lU.a,_lZ.a));}}}},_m0=function(_m1,_m2,_m3){while(1){if(!E(_lQ)){if(!B(_l3(B(_lc(_m2,_lP)),_lb))){if(!B(_l3(_m2,_lM))){var _m4=B(_aS(_m1,_m1)),_m5=B(_lx(B(_lR(_m2,_lM)),_lP)),_m6=B(_aS(_m1,_m3));_m1=_m4;_m2=_m5;_m3=_m6;continue;}else{return new F(function(){return _aS(_m1,_m3);});}}else{var _m4=B(_aS(_m1,_m1)),_m5=B(_lx(_m2,_lP));_m1=_m4;_m2=_m5;continue;}}else{return E(_l2);}}},_m7=function(_m8,_m9){while(1){if(!E(_lQ)){if(!B(_l3(B(_lc(_m9,_lP)),_lb))){if(!B(_l3(_m9,_lM))){return new F(function(){return _m0(B(_aS(_m8,_m8)),B(_lx(B(_lR(_m9,_lM)),_lP)),_m8);});}else{return E(_m8);}}else{var _ma=B(_aS(_m8,_m8)),_mb=B(_lx(_m9,_lP));_m8=_ma;_m9=_mb;continue;}}else{return E(_l2);}}},_mc=function(_md,_me){var _mf=E(_md);if(!_mf._){var _mg=_mf.a,_mh=E(_me);return (_mh._==0)?_mg<_mh.a:I_compareInt(_mh.a,_mg)>0;}else{var _mi=_mf.a,_mj=E(_me);return (_mj._==0)?I_compareInt(_mi,_mj.a)<0:I_compare(_mi,_mj.a)<0;}},_mk=function(_ml,_mm){if(!B(_mc(_mm,_lb))){if(!B(_l3(_mm,_lb))){return new F(function(){return _m7(_ml,_mm);});}else{return E(_lM);}}else{return E(_lO);}},_mn=new T1(0,1),_mo=new T1(0,0),_mp=new T1(0,-1),_mq=function(_mr){var _ms=E(_mr);if(!_ms._){var _mt=_ms.a;return (_mt>=0)?(E(_mt)==0)?E(_mo):E(_am):E(_mp);}else{var _mu=I_compareInt(_ms.a,0);return (_mu<=0)?(E(_mu)==0)?E(_mo):E(_mp):E(_am);}},_mv=function(_mw,_mx,_my){while(1){var _mz=E(_my);if(!_mz._){if(!B(_mc(_mw,_b5))){return new T2(0,B(_aS(_mx,B(_mk(_aC,_mw)))),_lM);}else{var _mA=B(_mk(_aC,B(_ay(_mw))));return new F(function(){return _lI(B(_aS(_mx,B(_mq(_mA)))),B(_ls(_mA)));});}}else{var _mB=B(_lR(_mw,_mn)),_mC=B(_ao(B(_aS(_mx,_aC)),B(_aM(E(_mz.a)))));_mw=_mB;_mx=_mC;_my=_mz.b;continue;}}},_mD=function(_mE,_mF){var _mG=E(_mE);if(!_mG._){var _mH=_mG.a,_mI=E(_mF);return (_mI._==0)?_mH>=_mI.a:I_compareInt(_mI.a,_mH)<=0;}else{var _mJ=_mG.a,_mK=E(_mF);return (_mK._==0)?I_compareInt(_mJ,_mK.a)>=0:I_compare(_mJ,_mK.a)>=0;}},_mL=function(_mM){var _mN=E(_mM);if(!_mN._){var _mO=_mN.b;return new F(function(){return _lI(B(_aS(B(_b6(new T(function(){return B(_aM(E(_mN.a)));}),new T(function(){return B(_aD(_mO,0));},1),B(_aI(_aO,_mO)))),_mn)),_mn);});}else{var _mP=_mN.a,_mQ=_mN.c,_mR=E(_mN.b);if(!_mR._){var _mS=E(_mQ);if(!_mS._){return new F(function(){return _lI(B(_aS(B(_bn(_aC,_mP)),_mn)),_mn);});}else{var _mT=_mS.a;if(!B(_mD(_mT,_b5))){var _mU=B(_mk(_aC,B(_ay(_mT))));return new F(function(){return _lI(B(_aS(B(_bn(_aC,_mP)),B(_mq(_mU)))),B(_ls(_mU)));});}else{return new F(function(){return _lI(B(_aS(B(_aS(B(_bn(_aC,_mP)),B(_mk(_aC,_mT)))),_mn)),_mn);});}}}else{var _mV=_mR.a,_mW=E(_mQ);if(!_mW._){return new F(function(){return _mv(_b5,B(_bn(_aC,_mP)),_mV);});}else{return new F(function(){return _mv(_mW.a,B(_bn(_aC,_mP)),_mV);});}}}},_mX=function(_mY,_mZ){while(1){var _n0=E(_mZ);if(!_n0._){return __Z;}else{if(!B(A1(_mY,_n0.a))){return E(_n0);}else{_mZ=_n0.b;continue;}}}},_n1=function(_n2,_n3){var _n4=E(_n2);if(!_n4._){var _n5=_n4.a,_n6=E(_n3);return (_n6._==0)?_n5>_n6.a:I_compareInt(_n6.a,_n5)<0;}else{var _n7=_n4.a,_n8=E(_n3);return (_n8._==0)?I_compareInt(_n7,_n8.a)>0:I_compare(_n7,_n8.a)>0;}},_n9=0,_na=function(_nb,_nc){return E(_nb)==E(_nc);},_nd=function(_ne){return new F(function(){return _na(_n9,_ne);});},_nf=new T2(0,E(_b5),E(_lM)),_ng=new T1(1,_nf),_nh=new T1(0,-2147483648),_ni=new T1(0,2147483647),_nj=function(_nk,_nl,_nm){var _nn=E(_nm);if(!_nn._){return new T1(1,new T(function(){var _no=B(_mL(_nn));return new T2(0,E(_no.a),E(_no.b));}));}else{var _np=E(_nn.c);if(!_np._){return new T1(1,new T(function(){var _nq=B(_mL(_nn));return new T2(0,E(_nq.a),E(_nq.b));}));}else{var _nr=_np.a;if(!B(_n1(_nr,_ni))){if(!B(_mc(_nr,_nh))){var _ns=function(_nt){var _nu=_nt+B(_cj(_nr))|0;return (_nu<=(E(_nl)+3|0))?(_nu>=(E(_nk)-3|0))?new T1(1,new T(function(){var _nv=B(_mL(_nn));return new T2(0,E(_nv.a),E(_nv.b));})):E(_ng):__Z;},_nw=B(_mX(_nd,_nn.a));if(!_nw._){var _nx=E(_nn.b);if(!_nx._){return E(_ng);}else{var _ny=B(_6L(_nd,_nx.a));if(!E(_ny.b)._){return E(_ng);}else{return new F(function(){return _ns( -B(_aD(_ny.a,0)));});}}}else{return new F(function(){return _ns(B(_aD(_nw,0)));});}}else{return __Z;}}else{return __Z;}}}},_nz=function(_nA,_nB){return new T0(2);},_nC=new T1(0,1),_nD=function(_nE,_nF){var _nG=E(_nE);if(!_nG._){var _nH=_nG.a,_nI=E(_nF);if(!_nI._){var _nJ=_nI.a;return (_nH!=_nJ)?(_nH>_nJ)?2:0:1;}else{var _nK=I_compareInt(_nI.a,_nH);return (_nK<=0)?(_nK>=0)?1:2:0;}}else{var _nL=_nG.a,_nM=E(_nF);if(!_nM._){var _nN=I_compareInt(_nL,_nM.a);return (_nN>=0)?(_nN<=0)?1:2:0;}else{var _nO=I_compare(_nL,_nM.a);return (_nO>=0)?(_nO<=0)?1:2:0;}}},_nP=function(_nQ,_nR){var _nS=E(_nQ);return (_nS._==0)?_nS.a*Math.pow(2,_nR):I_toNumber(_nS.a)*Math.pow(2,_nR);},_nT=function(_nU,_nV){while(1){var _nW=E(_nU);if(!_nW._){var _nX=E(_nW.a);if(_nX==(-2147483648)){_nU=new T1(1,I_fromInt(-2147483648));continue;}else{var _nY=E(_nV);if(!_nY._){var _nZ=_nY.a;return new T2(0,new T1(0,quot(_nX,_nZ)),new T1(0,_nX%_nZ));}else{_nU=new T1(1,I_fromInt(_nX));_nV=_nY;continue;}}}else{var _o0=E(_nV);if(!_o0._){_nU=_nW;_nV=new T1(1,I_fromInt(_o0.a));continue;}else{var _o1=I_quotRem(_nW.a,_o0.a);return new T2(0,new T1(1,_o1.a),new T1(1,_o1.b));}}}},_o2=new T1(0,0),_o3=function(_o4,_o5){while(1){var _o6=E(_o4);if(!_o6._){_o4=new T1(1,I_fromInt(_o6.a));continue;}else{return new T1(1,I_shiftLeft(_o6.a,_o5));}}},_o7=function(_o8,_o9,_oa){if(!B(_l3(_oa,_o2))){var _ob=B(_nT(_o9,_oa)),_oc=_ob.a;switch(B(_nD(B(_o3(_ob.b,1)),_oa))){case 0:return new F(function(){return _nP(_oc,_o8);});break;case 1:if(!(B(_cj(_oc))&1)){return new F(function(){return _nP(_oc,_o8);});}else{return new F(function(){return _nP(B(_ao(_oc,_nC)),_o8);});}break;default:return new F(function(){return _nP(B(_ao(_oc,_nC)),_o8);});}}else{return E(_l2);}},_od=function(_oe){var _of=function(_og,_oh){while(1){if(!B(_mc(_og,_oe))){if(!B(_n1(_og,_oe))){if(!B(_l3(_og,_oe))){return new F(function(){return _77("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_oh);}}else{return _oh-1|0;}}else{var _oi=B(_o3(_og,1)),_oj=_oh+1|0;_og=_oi;_oh=_oj;continue;}}};return new F(function(){return _of(_am,0);});},_ok=function(_ol){var _om=E(_ol);if(!_om._){var _on=_om.a>>>0;if(!_on){return -1;}else{var _oo=function(_op,_oq){while(1){if(_op>=_on){if(_op<=_on){if(_op!=_on){return new F(function(){return _77("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");});}else{return E(_oq);}}else{return _oq-1|0;}}else{var _or=imul(_op,2)>>>0,_os=_oq+1|0;_op=_or;_oq=_os;continue;}}};return new F(function(){return _oo(1,0);});}}else{return new F(function(){return _od(_om);});}},_ot=function(_ou){var _ov=E(_ou);if(!_ov._){var _ow=_ov.a>>>0;if(!_ow){return new T2(0,-1,0);}else{var _ox=function(_oy,_oz){while(1){if(_oy>=_ow){if(_oy<=_ow){if(_oy!=_ow){return new F(function(){return _77("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");});}else{return E(_oz);}}else{return _oz-1|0;}}else{var _oA=imul(_oy,2)>>>0,_oB=_oz+1|0;_oy=_oA;_oz=_oB;continue;}}};return new T2(0,B(_ox(1,0)),(_ow&_ow-1>>>0)>>>0&4294967295);}}else{var _oC=B(_ok(_ov)),_oD=_oC>>>0;if(!_oD){var _oE=E(_oC);return (_oE==(-2))?new T2(0,-2,0):new T2(0,_oE,1);}else{var _oF=function(_oG,_oH){while(1){if(_oG>=_oD){if(_oG<=_oD){if(_oG!=_oD){return new F(function(){return _77("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");});}else{return E(_oH);}}else{return _oH-1|0;}}else{var _oI=imul(_oG,2)>>>0,_oJ=_oH+1|0;_oG=_oI;_oH=_oJ;continue;}}},_oK=B(_oF(1,0));return ((_oK+_oK|0)!=_oC)?new T2(0,_oC,1):new T2(0,_oC,0);}}},_oL=function(_oM,_oN){while(1){var _oO=E(_oM);if(!_oO._){var _oP=_oO.a,_oQ=E(_oN);if(!_oQ._){return new T1(0,(_oP>>>0&_oQ.a>>>0)>>>0&4294967295);}else{_oM=new T1(1,I_fromInt(_oP));_oN=_oQ;continue;}}else{var _oR=E(_oN);if(!_oR._){_oM=_oO;_oN=new T1(1,I_fromInt(_oR.a));continue;}else{return new T1(1,I_and(_oO.a,_oR.a));}}}},_oS=new T1(0,2),_oT=function(_oU,_oV){var _oW=E(_oU);if(!_oW._){var _oX=(_oW.a>>>0&(2<<_oV>>>0)-1>>>0)>>>0,_oY=1<<_oV>>>0;return (_oY<=_oX)?(_oY>=_oX)?1:2:0;}else{var _oZ=B(_oL(_oW,B(_lR(B(_o3(_oS,_oV)),_am)))),_p0=B(_o3(_am,_oV));return (!B(_n1(_p0,_oZ)))?(!B(_mc(_p0,_oZ)))?1:2:0;}},_p1=function(_p2,_p3){while(1){var _p4=E(_p2);if(!_p4._){_p2=new T1(1,I_fromInt(_p4.a));continue;}else{return new T1(1,I_shiftRight(_p4.a,_p3));}}},_p5=function(_p6,_p7,_p8,_p9){var _pa=B(_ot(_p9)),_pb=_pa.a;if(!E(_pa.b)){var _pc=B(_ok(_p8));if(_pc<((_pb+_p6|0)-1|0)){var _pd=_pb+(_p6-_p7|0)|0;if(_pd>0){if(_pd>_pc){if(_pd<=(_pc+1|0)){if(!E(B(_ot(_p8)).b)){return 0;}else{return new F(function(){return _nP(_nC,_p6-_p7|0);});}}else{return 0;}}else{var _pe=B(_p1(_p8,_pd));switch(B(_oT(_p8,_pd-1|0))){case 0:return new F(function(){return _nP(_pe,_p6-_p7|0);});break;case 1:if(!(B(_cj(_pe))&1)){return new F(function(){return _nP(_pe,_p6-_p7|0);});}else{return new F(function(){return _nP(B(_ao(_pe,_nC)),_p6-_p7|0);});}break;default:return new F(function(){return _nP(B(_ao(_pe,_nC)),_p6-_p7|0);});}}}else{return new F(function(){return _nP(_p8,(_p6-_p7|0)-_pd|0);});}}else{if(_pc>=_p7){var _pf=B(_p1(_p8,(_pc+1|0)-_p7|0));switch(B(_oT(_p8,_pc-_p7|0))){case 0:return new F(function(){return _nP(_pf,((_pc-_pb|0)+1|0)-_p7|0);});break;case 2:return new F(function(){return _nP(B(_ao(_pf,_nC)),((_pc-_pb|0)+1|0)-_p7|0);});break;default:if(!(B(_cj(_pf))&1)){return new F(function(){return _nP(_pf,((_pc-_pb|0)+1|0)-_p7|0);});}else{return new F(function(){return _nP(B(_ao(_pf,_nC)),((_pc-_pb|0)+1|0)-_p7|0);});}}}else{return new F(function(){return _nP(_p8, -_pb);});}}}else{var _pg=B(_ok(_p8))-_pb|0,_ph=function(_pi){var _pj=function(_pk,_pl){if(!B(_cm(B(_o3(_pl,_p7)),_pk))){return new F(function(){return _o7(_pi-_p7|0,_pk,_pl);});}else{return new F(function(){return _o7((_pi-_p7|0)+1|0,_pk,B(_o3(_pl,1)));});}};if(_pi>=_p7){if(_pi!=_p7){return new F(function(){return _pj(_p8,new T(function(){return B(_o3(_p9,_pi-_p7|0));}));});}else{return new F(function(){return _pj(_p8,_p9);});}}else{return new F(function(){return _pj(new T(function(){return B(_o3(_p8,_p7-_pi|0));}),_p9);});}};if(_p6>_pg){return new F(function(){return _ph(_p6);});}else{return new F(function(){return _ph(_pg);});}}},_pm=new T(function(){return 0/0;}),_pn=new T(function(){return -1/0;}),_po=new T(function(){return 1/0;}),_pp=0,_pq=function(_pr,_ps){if(!B(_l3(_ps,_o2))){if(!B(_l3(_pr,_o2))){if(!B(_mc(_pr,_o2))){return new F(function(){return _p5(-1021,53,_pr,_ps);});}else{return  -B(_p5(-1021,53,B(_ay(_pr)),_ps));}}else{return E(_pp);}}else{return (!B(_l3(_pr,_o2)))?(!B(_mc(_pr,_o2)))?E(_po):E(_pn):E(_pm);}},_pt=function(_pu){var _pv=E(_pu);switch(_pv._){case 3:var _pw=_pv.a;return (!B(_7Y(_pw,_kr)))?(!B(_7Y(_pw,_kq)))?E(_nz):E(_kn):E(_kj);case 5:var _px=B(_nj(_kt,_ks,_pv.a));if(!_px._){return E(_kj);}else{var _py=new T(function(){var _pz=E(_px.a);return B(_pq(_pz.a,_pz.b));});return function(_pA,_pB){return new F(function(){return A1(_pB,_py);});};}break;default:return E(_nz);}},_pC=function(_pD){var _pE=function(_pF){return E(new T2(3,_pD,_8u));};return new T1(1,function(_pG){return new F(function(){return A2(_hC,_pG,_pE);});});},_pH=new T(function(){return B(A3(_jX,_pt,_js,_pC));}),_pI=new T(function(){return B(unCStr("height"));}),_pJ=function(_pK){while(1){var _pL=B((function(_pM){var _pN=E(_pM);if(!_pN._){return __Z;}else{var _pO=_pN.b,_pP=E(_pN.a);if(!E(_pP.b)._){return new T2(1,_pP.a,new T(function(){return B(_pJ(_pO));}));}else{_pK=_pO;return __continue;}}})(_pK));if(_pL!=__continue){return _pL;}}},_pQ=function(_pR,_){var _pS=B(A(_5Y,[_5F,_2v,_pR,_68,_])),_pT=B(A(_5Y,[_5F,_2v,_pR,_pI,_]));return new T2(0,new T(function(){var _pU=B(_pJ(B(_7a(_pH,_pS))));if(!_pU._){return E(_6c);}else{if(!E(_pU.b)._){return E(_pU.a);}else{return E(_6a);}}}),new T(function(){var _pV=B(_pJ(B(_7a(_pH,_pT))));if(!_pV._){return E(_6c);}else{if(!E(_pV.b)._){return E(_pV.a);}else{return E(_6a);}}}));},_pW=function(_pX){return E(E(_pX).a);},_pY=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_pZ=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_q0=function(_q1){return E(E(_q1).b);},_q2=function(_q3,_q4,_q5){var _q6=B(_pW(_q3)),_q7=new T(function(){return B(_2D(_q6));}),_q8=function(_q9){var _qa=function(_){var _qb=E(_q4);if(!_qb._){var _qc=B(A1(_q9,_2Q)),_qd=__createJSFunc(0,function(_){var _qe=B(A1(_qc,_));return _2C;}),_qf=__app2(E(_pZ),_qb.a,_qd);return new T(function(){var _qg=Number(_qf),_qh=jsTrunc(_qg);return new T2(0,_qh,E(_qb));});}else{var _qi=B(A1(_q9,_2Q)),_qj=__createJSFunc(0,function(_){var _qk=B(A1(_qi,_));return _2C;}),_ql=__app2(E(_pY),_qb.a,_qj);return new T(function(){var _qm=Number(_ql),_qn=jsTrunc(_qm);return new T2(0,_qn,E(_qb));});}};return new F(function(){return A1(_q7,_qa);});},_qo=new T(function(){return B(A2(_q0,_q3,function(_qp){return E(_q5);}));});return new F(function(){return A3(_5I,B(_5G(_q6)),_qo,_q8);});},_qq=function(_qr){return E(E(_qr).b);},_qs=new T2(1,_v,_v),_qt=function(_qu,_qv){var _qw=function(_qx,_qy){var _qz=E(_qx);if(!_qz._){return E(_qy);}else{var _qA=_qz.a,_qB=E(_qy);if(!_qB._){return E(_qz);}else{var _qC=_qB.a;return (B(A2(_qu,_qA,_qC))==2)?new T2(1,_qC,new T(function(){return B(_qw(_qz,_qB.b));})):new T2(1,_qA,new T(function(){return B(_qw(_qz.b,_qB));}));}}},_qD=function(_qE){var _qF=E(_qE);if(!_qF._){return __Z;}else{var _qG=E(_qF.b);return (_qG._==0)?E(_qF):new T2(1,new T(function(){return B(_qw(_qF.a,_qG.a));}),new T(function(){return B(_qD(_qG.b));}));}},_qH=new T(function(){return B(_qI(B(_qD(_v))));}),_qI=function(_qJ){while(1){var _qK=E(_qJ);if(!_qK._){return E(_qH);}else{if(!E(_qK.b)._){return E(_qK.a);}else{_qJ=B(_qD(_qK));continue;}}}},_qL=new T(function(){return B(_qM(_v));}),_qN=function(_qO,_qP,_qQ){while(1){var _qR=B((function(_qS,_qT,_qU){var _qV=E(_qU);if(!_qV._){return new T2(1,new T2(1,_qS,_qT),_qL);}else{var _qW=_qV.a;if(B(A2(_qu,_qS,_qW))==2){var _qX=new T2(1,_qS,_qT);_qO=_qW;_qP=_qX;_qQ=_qV.b;return __continue;}else{return new T2(1,new T2(1,_qS,_qT),new T(function(){return B(_qM(_qV));}));}}})(_qO,_qP,_qQ));if(_qR!=__continue){return _qR;}}},_qY=function(_qZ,_r0,_r1){while(1){var _r2=B((function(_r3,_r4,_r5){var _r6=E(_r5);if(!_r6._){return new T2(1,new T(function(){return B(A1(_r4,new T2(1,_r3,_v)));}),_qL);}else{var _r7=_r6.a,_r8=_r6.b;switch(B(A2(_qu,_r3,_r7))){case 0:_qZ=_r7;_r0=function(_r9){return new F(function(){return A1(_r4,new T2(1,_r3,_r9));});};_r1=_r8;return __continue;case 1:_qZ=_r7;_r0=function(_ra){return new F(function(){return A1(_r4,new T2(1,_r3,_ra));});};_r1=_r8;return __continue;default:return new T2(1,new T(function(){return B(A1(_r4,new T2(1,_r3,_v)));}),new T(function(){return B(_qM(_r6));}));}}})(_qZ,_r0,_r1));if(_r2!=__continue){return _r2;}}},_qM=function(_rb){var _rc=E(_rb);if(!_rc._){return E(_qs);}else{var _rd=_rc.a,_re=E(_rc.b);if(!_re._){return new T2(1,_rc,_v);}else{var _rf=_re.a,_rg=_re.b;if(B(A2(_qu,_rd,_rf))==2){return new F(function(){return _qN(_rf,new T2(1,_rd,_v),_rg);});}else{return new F(function(){return _qY(_rf,function(_rh){return new T2(1,_rd,_rh);},_rg);});}}}};return new F(function(){return _qI(B(_qM(_qv)));});},_ri=function(_rj,_rk,_rl,_){var _rm=E(_3u),_rn=__app1(_rm,_rk),_ro=function(_rp,_rq,_){var _rr=E(_rp);if(!_rr._){return _v;}else{var _rs=E(_rr.a),_rt=_rs.a,_ru=E(_rs.c),_rv=_ru.a,_rw=_ru.b,_rx=function(_){var _ry=new T(function(){var _rz=E(_rt);return B(_3n(_rz.a,_rz.b,new T(function(){return B(_3h(0,E(_ru.d),_v));},1)));}),_rA=B(A(_50,[_5m,_ry,_rq,_])),_rB=B(_ro(_rr.b,_rq,_));return new T2(1,_rA,_rB);};if(!E(_ru.e)){var _rC=new T(function(){return E(_rv)*E(_rw);}),_rD=function(_rE,_){var _rF=E(_rt);return new F(function(){return _2W(E(_rF.a),E(_rF.b),E(_rC),E(_rE),_);});},_rG=B(A(_50,[_5k,function(_rH,_){return new F(function(){return _35(_rD,E(_rH),_);});},_rq,_]));return new F(function(){return _rx(_);});}else{var _rI=new T(function(){return E(_rv)*E(_rw);}),_rJ=function(_rK,_){var _rL=E(_rt);return new F(function(){return _2W(E(_rL.a),E(_rL.b),E(_rI),E(_rK),_);});},_rM=B(A(_50,[_5l,function(_rN,_){return new F(function(){return _35(_rJ,E(_rN),_);});},_rq,_]));return new F(function(){return _rx(_);});}}},_rO=B(_ro(_rl,_rj,_)),_rP=B(_pQ(new T2(0,_rj,_rk),_)),_rQ=_rP,_rR=function(_){var _rS=function(_rT,_rU,_){var _rV=E(_rT);if(!_rV._){return _v;}else{var _rW=E(_rV.a),_rX=_rW.a,_rY=E(_rW.c),_rZ=_rY.a,_s0=_rY.b,_s1=function(_){var _s2=new T(function(){var _s3=E(_rX);return B(_3n(_s3.a,_s3.b,new T(function(){return B(_3h(0,E(_rY.d),_v));},1)));}),_s4=B(A(_50,[_5m,_s2,_rU,_])),_s5=B(_rS(_rV.b,_rU,_));return new T2(1,_s4,_s5);};if(!E(_rY.e)){var _s6=new T(function(){return E(_rZ)*E(_s0);}),_s7=function(_s8,_){var _s9=E(_rX);return new F(function(){return _2W(E(_s9.a),E(_s9.b),E(_s6),E(_s8),_);});},_sa=B(A(_50,[_5k,function(_sb,_){return new F(function(){return _35(_s7,E(_sb),_);});},_rU,_]));return new F(function(){return _s1(_);});}else{var _sc=new T(function(){return E(_rZ)*E(_s0);}),_sd=function(_se,_){var _sf=E(_rX);return new F(function(){return _2W(E(_sf.a),E(_sf.b),E(_sc),E(_se),_);});},_sg=B(A(_50,[_5l,function(_sh,_){return new F(function(){return _35(_sd,E(_sh),_);});},_rU,_]));return new F(function(){return _s1(_);});}}},_si=function(_sj,_sk,_sl,_){var _sm=__app1(_rm,_sk),_sn=B(_rS(_sl,_sj,_)),_so=B(_pQ(new T2(0,_sj,_sk),_)),_sp=_so,_sq=function(_){var _sr=new T(function(){var _ss=function(_st){var _su=E(_st),_sv=_su.a,_sw=_su.b,_sx=_su.c,_sy=new T(function(){var _sz=E(E(_sv).a),_sA=E(_sx),_sB=E(E(_sw).a)*0.95,_sC=E(_sA.a)*E(_sA.b);if(_sz+_sB>=_sC){var _sD=E(E(_sp).a)-_sC;if(_sz+_sB<=_sD){return new T2(0,_sz+_sB,_sB);}else{return new T2(0,_sD+_sD-(_sz+_sB), -_sB);}}else{return new T2(0,_sC+_sC-(_sz+_sB), -_sB);}}),_sE=new T(function(){var _sF=E(E(_sv).b),_sG=E(_sx),_sH=E(E(_sw).b)*0.95,_sI=E(_sG.a)*E(_sG.b);if(_sF+_sH>=_sI){var _sJ=E(E(_sp).b)-_sI;if(_sF+_sH<=_sJ){return new T2(0,_sF+_sH,_sH);}else{return new T2(0,_sJ+_sJ-(_sF+_sH), -_sH);}}else{return new T2(0,_sI+_sI-(_sF+_sH), -_sH);}});return new T3(0,new T2(0,new T(function(){return E(E(_sy).a);}),new T(function(){return E(E(_sE).a);})),new T2(0,new T(function(){return E(E(_sy).b);}),new T(function(){return E(E(_sE).b);})),_sx);};return B(_aI(_ss,B(_3v(B(_aI(_qq,B(_qt(_5s,B(_aI(_5o,_sl))))))))));});return new F(function(){return _si(_sj,_sk,_sr,_);});},_sK=B(A(_q2,[_2P,_5n,_sq,_]));return _2Q;},_sL=new T(function(){var _sM=function(_sN){var _sO=E(_sN),_sP=_sO.a,_sQ=_sO.b,_sR=_sO.c,_sS=new T(function(){var _sT=E(E(_sP).a),_sU=E(_sR),_sV=E(E(_sQ).a)*0.95,_sW=E(_sU.a)*E(_sU.b);if(_sT+_sV>=_sW){var _sX=E(E(_rQ).a)-_sW;if(_sT+_sV<=_sX){return new T2(0,_sT+_sV,_sV);}else{return new T2(0,_sX+_sX-(_sT+_sV), -_sV);}}else{return new T2(0,_sW+_sW-(_sT+_sV), -_sV);}}),_sY=new T(function(){var _sZ=E(E(_sP).b),_t0=E(_sR),_t1=E(E(_sQ).b)*0.95,_t2=E(_t0.a)*E(_t0.b);if(_sZ+_t1>=_t2){var _t3=E(E(_rQ).b)-_t2;if(_sZ+_t1<=_t3){return new T2(0,_sZ+_t1,_t1);}else{return new T2(0,_t3+_t3-(_sZ+_t1), -_t1);}}else{return new T2(0,_t2+_t2-(_sZ+_t1), -_t1);}});return new T3(0,new T2(0,new T(function(){return E(E(_sS).a);}),new T(function(){return E(E(_sY).a);})),new T2(0,new T(function(){return E(E(_sS).b);}),new T(function(){return E(E(_sY).b);})),_sR);};return B(_aI(_sM,B(_3v(B(_aI(_qq,B(_qt(_5s,B(_aI(_5o,_rl))))))))));});return new F(function(){return _si(_rj,_rk,_sL,_);});},_t4=B(A(_q2,[_2P,_5n,_rR,_]));return _2Q;},_t5=function(_t6,_t7){var _t8=new T(function(){var _t9=B(_t5(_t6,new T(function(){return B(A1(_t6,_t7));})));return new T2(1,_t9.a,_t9.b);});return new T2(0,_t7,_t8);},_ta=new T(function(){return B(unCStr("Pattern match failure in do expression at barshare.hs:130:3-10"));}),_tb=new T6(0,_2d,_2e,_v,_ta,_2d,_2d),_tc=new T(function(){return B(_1G(_tb));}),_td=100,_te=new T2(0,_td,_td),_tf=1,_tg=1,_th=new T(function(){return B(unCStr("banana"));}),_ti=7,_tj=9,_tk=new T5(0,_tj,_ti,_th,_tg,_tf),_tl=function(_tm){var _tn=E(_tm);return (_tn==1)?new T2(0,_tk,_v):new T2(0,_tk,new T(function(){var _to=B(_tl(_tn-1|0));return new T2(1,_to.a,_to.b);}));},_tp=new T(function(){var _tq=B(_tl(10));return new T2(1,_tq.a,_tq.b);}),_tr=new T(function(){return B(_aD(_tp,0));}),_ts=function(_tt,_tu){return E(_tt)+E(_tu);},_tv=function(_,_tw){var _tx=E(_tw);if(!_tx._){return new F(function(){return die(_tc);});}else{var _ty=_tx.a,_tz=B(_pQ(_ty,_)),_tA=E(_tz),_tB=E(_ty),_tC=new T(function(){var _tD=new T(function(){return E(_tA.b)/(E(_tr)+1);}),_tE=B(_t5(function(_tF){return new F(function(){return _ts(_tF,_tD);});},_tD)),_tG=new T(function(){return E(_tA.a)/(E(_tr)+1);}),_tH=function(_tI,_tJ,_tK){var _tL=E(_tJ);if(!_tL._){return __Z;}else{var _tM=E(_tK);if(!_tM._){return __Z;}else{var _tN=new T(function(){return B(_tH(new T(function(){return E(_tI)+E(_tG);}),_tL.b,_tM.b));});return new T2(1,new T3(0,new T2(0,_tI,_tL.a),_te,_tM.a),_tN);}}},_tO=function(_tP,_tQ,_tR,_tS){var _tT=E(_tS);if(!_tT._){return __Z;}else{var _tU=new T(function(){return B(_tH(new T(function(){return E(_tP)+E(_tG);}),_tR,_tT.b));});return new T2(1,new T3(0,new T2(0,_tP,_tQ),_te,_tT.a),_tU);}};return B(_tO(_tG,_tE.a,_tE.b,_tp));});return new F(function(){return _ri(_tB.a,_tB.b,_tC,_);});}},_tV=function(_){var _tW=B(A3(_2F,_2v,_2O,_)),_tX=E(_tW);if(!_tX._){return new F(function(){return die(_2N);});}else{var _tY=E(_tX.a),_tZ=__app1(E(_1),_tY);if(!_tZ){return new F(function(){return _tv(_,_2d);});}else{var _u0=__app1(E(_0),_tY);return new F(function(){return _tv(_,new T1(1,new T2(0,_u0,_tY)));});}}},_u1=function(_){return new F(function(){return _tV(_);});};
var hasteMain = function() {B(A(_u1, [0]));};window.onload = hasteMain;