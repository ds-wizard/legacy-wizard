"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

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

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
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
    return {_:0, a:I_div(a,b), b:a.mod(b)};
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
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

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

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
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

var _0/* () */ = 0,
_1/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _0/* GHC.Tuple.() */;
},
_2/* errorIO2 */ = "(function (s) { console.error(s); })",
_3/* errorIO1 */ = function(_4/* sjYI */, _/* EXTERNAL */){
  var _5/* sjYS */ = eval/* EXTERNAL */(E(_2/* FormEngine.JQuery.errorIO2 */)),
  _6/* sjZ0 */ = __app1/* EXTERNAL */(E(_5/* sjYS */), toJSStr/* EXTERNAL */(E(_4/* sjYI */)));
  return _0/* GHC.Tuple.() */;
},
_7/* ++ */ = function(_8/* s3hJ */, _9/* s3hK */){
  var _a/* s3hL */ = E(_8/* s3hJ */);
  return (_a/* s3hL */._==0) ? E(_9/* s3hK */) : new T2(1,_a/* s3hL */.a,new T(function(){
    return B(_7/* GHC.Base.++ */(_a/* s3hL */.b, _9/* s3hK */));
  }));
},
_b/* $fHasChildrenFormElement_go */ = function(_c/*  sbOI */, _d/*  sbOJ */){
  while(1){
    var _e/*  $fHasChildrenFormElement_go */ = B((function(_f/* sbOI */, _g/* sbOJ */){
      var _h/* sbOK */ = E(_f/* sbOI */);
      if(!_h/* sbOK */._){
        return E(_g/* sbOJ */);
      }else{
        var _i/*   sbOJ */ = B(_7/* GHC.Base.++ */(_g/* sbOJ */, new T(function(){
          var _j/* sbON */ = E(_h/* sbOK */.a);
          if(!_j/* sbON */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_j/* sbON */.c);
          }
        },1)));
        _c/*  sbOI */ = _h/* sbOK */.b;
        _d/*  sbOJ */ = _i/*   sbOJ */;
        return __continue/* EXTERNAL */;
      }
    })(_c/*  sbOI */, _d/*  sbOJ */));
    if(_e/*  $fHasChildrenFormElement_go */!=__continue/* EXTERNAL */){
      return _e/*  $fHasChildrenFormElement_go */;
    }
  }
},
_k/* [] */ = __Z/* EXTERNAL */,
_l/* $fHasChildrenFormElement_$cchildren */ = function(_m/* sbOV */){
  var _n/* sbOW */ = E(_m/* sbOV */);
  switch(_n/* sbOW */._){
    case 0:
      return E(_n/* sbOW */.b);
    case 5:
      return new F(function(){return _b/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go */(_n/* sbOW */.b, _k/* GHC.Types.[] */);});
      break;
    case 7:
      return E(_n/* sbOW */.b);
    case 8:
      return E(_n/* sbOW */.c);
    case 9:
      return E(_n/* sbOW */.b);
    default:
      return __Z/* EXTERNAL */;
  }
},
_o/* addClass2 */ = "(function (cls, jq) { jq.addClass(cls); return jq; })",
_p/* $wa */ = function(_q/* skfl */, _r/* skfm */, _/* EXTERNAL */){
  var _s/* skfw */ = eval/* EXTERNAL */(E(_o/* FormEngine.JQuery.addClass2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_s/* skfw */), toJSStr/* EXTERNAL */(E(_q/* skfl */)), _r/* skfm */);});
},
_t/* disableJq5 */ = "(function (k, v, jq) { jq.attr(k, v); return jq; })",
_u/* $wa6 */ = function(_v/* skgA */, _w/* skgB */, _x/* skgC */, _/* EXTERNAL */){
  var _y/* skgR */ = eval/* EXTERNAL */(E(_t/* FormEngine.JQuery.disableJq5 */));
  return new F(function(){return __app3/* EXTERNAL */(E(_y/* skgR */), toJSStr/* EXTERNAL */(E(_v/* skgA */)), toJSStr/* EXTERNAL */(E(_w/* skgB */)), _x/* skgC */);});
},
_z/* addClassInside_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.parent(); })");
}),
_A/* addClassInside_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.last(); })");
}),
_B/* addClassInside_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.children(); })");
}),
_C/* $wa20 */ = function(_D/* skh9 */, _E/* skha */, _F/* skhb */, _/* EXTERNAL */){
  var _G/* skhg */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _F/* skhb */),
  _H/* skhm */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _G/* skhg */),
  _I/* skhp */ = B(_u/* FormEngine.JQuery.$wa6 */(_D/* skh9 */, _E/* skha */, _H/* skhm */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_I/* skhp */));});
},
_J/* appearJq5 */ = "(function (key, val, jq) { jq.css(key, val); return jq; })",
_K/* $wa2 */ = function(_L/* skhK */, _M/* skhL */, _N/* skhM */, _/* EXTERNAL */){
  var _O/* ski1 */ = eval/* EXTERNAL */(E(_J/* FormEngine.JQuery.appearJq5 */));
  return new F(function(){return __app3/* EXTERNAL */(E(_O/* ski1 */), toJSStr/* EXTERNAL */(E(_L/* skhK */)), toJSStr/* EXTERNAL */(E(_M/* skhL */)), _N/* skhM */);});
},
_P/* $wa24 */ = function(_Q/* skiq */, _R/* skir */, _S/* skis */, _/* EXTERNAL */){
  var _T/* skix */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _S/* skis */),
  _U/* skiD */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _T/* skix */),
  _V/* skiG */ = B(_K/* FormEngine.JQuery.$wa2 */(_Q/* skiq */, _R/* skir */, _U/* skiD */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_V/* skiG */));});
},
_W/* appendT2 */ = "(function (tag, jq) { return jq.append(tag); })",
_X/* $wa3 */ = function(_Y/* skel */, _Z/* skem */, _/* EXTERNAL */){
  var _10/* skew */ = eval/* EXTERNAL */(E(_W/* FormEngine.JQuery.appendT2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_10/* skew */), toJSStr/* EXTERNAL */(E(_Y/* skel */)), _Z/* skem */);});
},
_11/* setText2 */ = "(function (txt, jq) { jq.text(txt); return jq; })",
_12/* $wa34 */ = function(_13/* skld */, _14/* skle */, _/* EXTERNAL */){
  var _15/* sklj */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _14/* skle */),
  _16/* sklp */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _15/* sklj */),
  _17/* sklA */ = eval/* EXTERNAL */(E(_11/* FormEngine.JQuery.setText2 */)),
  _18/* sklI */ = __app2/* EXTERNAL */(E(_17/* sklA */), toJSStr/* EXTERNAL */(E(_13/* skld */)), _16/* sklp */);
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), _18/* sklI */);});
},
_19/* appendJq_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq, toJq) { return toJq.append(jq); })");
}),
_1a/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<ul>"));
}),
_1b/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("nav"));
}),
_1c/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<li>"));
}),
_1d/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_1e/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<a>"));
}),
_1f/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'stripe stripe-thin\'>"));
}),
_1g/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_1h/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_1i/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("class"));
}),
_1j/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inside-bordered"));
}),
_1k/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_1l/* unsafeDupablePerformIO */ = function(_1m/* s2Wdd */){
  var _1n/* s2Wde */ = B(A1(_1m/* s2Wdd */,_/* EXTERNAL */));
  return E(_1n/* s2Wde */);
},
_1o/* nullValue */ = new T(function(){
  return B(_1l/* GHC.IO.unsafeDupablePerformIO */(_1k/* Haste.Prim.Any.lvl2 */));
}),
_1p/* jsNull */ = new T(function(){
  return E(_1o/* Haste.Prim.Any.nullValue */);
}),
_1q/* onClick2 */ = "(function (ev, jq) { jq.click(ev); })",
_1r/* onClick1 */ = function(_1s/* sjTQ */, _1t/* sjTR */, _/* EXTERNAL */){
  var _1u/* sjU3 */ = __createJSFunc/* EXTERNAL */(2, function(_1v/* sjTU */, _/* EXTERNAL */){
    var _1w/* sjTW */ = B(A2(E(_1s/* sjTQ */),_1v/* sjTU */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _1x/* sjU6 */ = E(_1t/* sjTR */),
  _1y/* sjUb */ = eval/* EXTERNAL */(E(_1q/* FormEngine.JQuery.onClick2 */)),
  _1z/* sjUj */ = __app2/* EXTERNAL */(E(_1y/* sjUb */), _1u/* sjU3 */, _1x/* sjU6 */);
  return _1x/* sjU6 */;
},
_1A/* fiDescriptor */ = function(_1B/* s4W3 */){
  var _1C/* s4W4 */ = E(_1B/* s4W3 */);
  switch(_1C/* s4W4 */._){
    case 0:
      return E(_1C/* s4W4 */.a);
    case 1:
      return E(_1C/* s4W4 */.a);
    case 2:
      return E(_1C/* s4W4 */.a);
    case 3:
      return E(_1C/* s4W4 */.a);
    case 4:
      return E(_1C/* s4W4 */.a);
    case 5:
      return E(_1C/* s4W4 */.a);
    case 6:
      return E(_1C/* s4W4 */.a);
    case 7:
      return E(_1C/* s4W4 */.a);
    case 8:
      return E(_1C/* s4W4 */.a);
    case 9:
      return E(_1C/* s4W4 */.a);
    case 10:
      return E(_1C/* s4W4 */.a);
    default:
      return E(_1C/* s4W4 */.a);
  }
},
_1D/* formItem */ = function(_1E/* sbMK */){
  var _1F/* sbML */ = E(_1E/* sbMK */);
  switch(_1F/* sbML */._){
    case 0:
      return E(_1F/* sbML */.a);
    case 1:
      return E(_1F/* sbML */.a);
    case 2:
      return E(_1F/* sbML */.a);
    case 3:
      return E(_1F/* sbML */.a);
    case 4:
      return E(_1F/* sbML */.a);
    case 5:
      return E(_1F/* sbML */.a);
    case 6:
      return E(_1F/* sbML */.a);
    case 7:
      return E(_1F/* sbML */.a);
    case 8:
      return E(_1F/* sbML */.a);
    case 9:
      return E(_1F/* sbML */.a);
    case 10:
      return E(_1F/* sbML */.a);
    default:
      return E(_1F/* sbML */.a);
  }
},
_1G/* itos */ = function(_1H/* sfbi */, _1I/* sfbj */){
  var _1J/* sfbl */ = jsShowI/* EXTERNAL */(_1H/* sfbi */);
  return new F(function(){return _7/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_1J/* sfbl */), _1I/* sfbj */);});
},
_1K/* shows7 */ = 41,
_1L/* shows8 */ = 40,
_1M/* $wshowSignedInt */ = function(_1N/* sfbq */, _1O/* sfbr */, _1P/* sfbs */){
  if(_1O/* sfbr */>=0){
    return new F(function(){return _1G/* GHC.Show.itos */(_1O/* sfbr */, _1P/* sfbs */);});
  }else{
    if(_1N/* sfbq */<=6){
      return new F(function(){return _1G/* GHC.Show.itos */(_1O/* sfbr */, _1P/* sfbs */);});
    }else{
      return new T2(1,_1L/* GHC.Show.shows8 */,new T(function(){
        var _1Q/* sfby */ = jsShowI/* EXTERNAL */(_1O/* sfbr */);
        return B(_7/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_1Q/* sfby */), new T2(1,_1K/* GHC.Show.shows7 */,_1P/* sfbs */)));
      }));
    }
  }
},
_1R/* $fShowInt_$cshow */ = function(_1S/* sffD */){
  return new F(function(){return _1M/* GHC.Show.$wshowSignedInt */(0, E(_1S/* sffD */), _k/* GHC.Types.[] */);});
},
_1T/* $wgo */ = function(_1U/* s4Xf */, _1V/* s4Xg */){
  var _1W/* s4Xh */ = E(_1U/* s4Xf */);
  if(!_1W/* s4Xh */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1X/* s4Xi */ = _1W/* s4Xh */.a,
    _1Y/* s4Xk */ = E(_1V/* s4Xg */);
    return (_1Y/* s4Xk */==1) ? new T2(1,new T(function(){
      return B(_1R/* GHC.Show.$fShowInt_$cshow */(_1X/* s4Xi */));
    }),_k/* GHC.Types.[] */) : new T2(1,new T(function(){
      return B(_1R/* GHC.Show.$fShowInt_$cshow */(_1X/* s4Xi */));
    }),new T(function(){
      return B(_1T/* FormEngine.FormItem.$wgo */(_1W/* s4Xh */.b, _1Y/* s4Xk */-1|0));
    }));
  }
},
_1Z/* intercalate1 */ = function(_20/* s1WJa */){
  var _21/* s1WJb */ = E(_20/* s1WJa */);
  if(!_21/* s1WJb */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _7/* GHC.Base.++ */(_21/* s1WJb */.a, new T(function(){
      return B(_1Z/* Data.OldList.intercalate1 */(_21/* s1WJb */.b));
    },1));});
  }
},
_22/* numbering2text1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_23/* prependToAll */ = function(_24/* s1WIX */, _25/* s1WIY */){
  var _26/* s1WIZ */ = E(_25/* s1WIY */);
  return (_26/* s1WIZ */._==0) ? __Z/* EXTERNAL */ : new T2(1,_24/* s1WIX */,new T2(1,_26/* s1WIZ */.a,new T(function(){
    return B(_23/* Data.OldList.prependToAll */(_24/* s1WIX */, _26/* s1WIZ */.b));
  })));
},
_27/* numbering2text */ = function(_28/* s4Xp */){
  var _29/* s4Xq */ = E(_28/* s4Xp */);
  if(!_29/* s4Xq */._){
    return __Z/* EXTERNAL */;
  }else{
    var _2a/* s4Xv */ = E(_29/* s4Xq */.b)+1|0;
    if(0>=_2a/* s4Xv */){
      return __Z/* EXTERNAL */;
    }else{
      var _2b/* s4Xy */ = B(_1T/* FormEngine.FormItem.$wgo */(_29/* s4Xq */.a, _2a/* s4Xv */));
      if(!_2b/* s4Xy */._){
        return __Z/* EXTERNAL */;
      }else{
        return new F(function(){return _1Z/* Data.OldList.intercalate1 */(new T2(1,_2b/* s4Xy */.a,new T(function(){
          return B(_23/* Data.OldList.prependToAll */(_22/* FormEngine.FormItem.numbering2text1 */, _2b/* s4Xy */.b));
        })));});
      }
    }
  }
},
_2c/* paneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pane_"));
}),
_2d/* paneId */ = function(_2e/* sftz */){
  return new F(function(){return _7/* GHC.Base.++ */(_2c/* FormEngine.FormElement.Identifiers.paneId1 */, new T(function(){
    return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2e/* sftz */)))).b));
  },1));});
},
_2f/* tabId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tab_"));
}),
_2g/* tabId */ = function(_2h/* sftO */){
  return new F(function(){return _7/* GHC.Base.++ */(_2f/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
    return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2h/* sftO */)))).b));
  },1));});
},
_2i/* tabName */ = function(_2j/* sfrm */){
  var _2k/* sfrA */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2j/* sfrm */)))).a);
  return (_2k/* sfrA */._==0) ? __Z/* EXTERNAL */ : E(_2k/* sfrA */.a);
},
_2l/* appearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("block"));
}),
_2m/* appearJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_2n/* eqString */ = function(_2o/* s3mQ */, _2p/* s3mR */){
  while(1){
    var _2q/* s3mS */ = E(_2o/* s3mQ */);
    if(!_2q/* s3mS */._){
      return (E(_2p/* s3mR */)._==0) ? true : false;
    }else{
      var _2r/* s3mY */ = E(_2p/* s3mR */);
      if(!_2r/* s3mY */._){
        return false;
      }else{
        if(E(_2q/* s3mS */.a)!=E(_2r/* s3mY */.a)){
          return false;
        }else{
          _2o/* s3mQ */ = _2q/* s3mS */.b;
          _2p/* s3mR */ = _2r/* s3mY */.b;
          continue;
        }
      }
    }
  }
},
_2s/* $fEqFormElement_$c== */ = function(_2t/* sbO4 */, _2u/* sbO5 */){
  return new F(function(){return _2n/* GHC.Base.eqString */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2t/* sbO4 */)))).b)), B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2u/* sbO5 */)))).b)));});
},
_2v/* removeClass2 */ = "(function (cls, jq) { jq.removeClass(cls); return jq; })",
_2w/* $wa16 */ = function(_2x/* skeQ */, _2y/* skeR */, _/* EXTERNAL */){
  var _2z/* skf1 */ = eval/* EXTERNAL */(E(_2v/* FormEngine.JQuery.removeClass2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_2z/* skf1 */), toJSStr/* EXTERNAL */(E(_2x/* skeQ */)), _2y/* skeR */);});
},
_2A/* colorizeTabs2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("notcurrent"));
}),
_2B/* colorizeTabs3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("current"));
}),
_2C/* colorizeTabs4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_2D/* select2 */ = "(function (elId) { var res = $(elId); if (res.length === 0) { console.warn(\'empty $ selection \' + elId); }; return res; })",
_2E/* select1 */ = function(_2F/* sk9Y */, _/* EXTERNAL */){
  var _2G/* ska8 */ = eval/* EXTERNAL */(E(_2D/* FormEngine.JQuery.select2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_2G/* ska8 */), toJSStr/* EXTERNAL */(E(_2F/* sk9Y */)));});
},
_2H/* colorizeTabs1 */ = function(_2I/* sgOT */, _2J/* sgOU */, _/* EXTERNAL */){
  var _2K/* sgOW */ = function(_2L/*  sgOX */, _/* EXTERNAL */){
    while(1){
      var _2M/*  sgOW */ = B((function(_2N/* sgOX */, _/* EXTERNAL */){
        var _2O/* sgOZ */ = E(_2N/* sgOX */);
        if(!_2O/* sgOZ */._){
          return _0/* GHC.Tuple.() */;
        }else{
          var _2P/* sgP0 */ = _2O/* sgOZ */.a,
          _2Q/* sgP1 */ = _2O/* sgOZ */.b;
          if(!B(_2s/* FormEngine.FormElement.FormElement.$fEqFormElement_$c== */(_2P/* sgP0 */, _2I/* sgOT */))){
            var _2R/* sgP5 */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_2P/* sgP0 */));
            },1))), _/* EXTERNAL */)),
            _2S/* sgPa */ = B(_2w/* FormEngine.JQuery.$wa16 */(_2B/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_2R/* sgP5 */), _/* EXTERNAL */)),
            _2T/* sgPf */ = B(_p/* FormEngine.JQuery.$wa */(_2A/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_2S/* sgPa */), _/* EXTERNAL */));
            _2L/*  sgOX */ = _2Q/* sgP1 */;
            return __continue/* EXTERNAL */;
          }else{
            var _2U/* sgPk */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_2P/* sgP0 */));
            },1))), _/* EXTERNAL */)),
            _2V/* sgPp */ = B(_2w/* FormEngine.JQuery.$wa16 */(_2A/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_2U/* sgPk */), _/* EXTERNAL */)),
            _2W/* sgPu */ = B(_p/* FormEngine.JQuery.$wa */(_2B/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_2V/* sgPp */), _/* EXTERNAL */));
            _2L/*  sgOX */ = _2Q/* sgP1 */;
            return __continue/* EXTERNAL */;
          }
        }
      })(_2L/*  sgOX */, _/* EXTERNAL */));
      if(_2M/*  sgOW */!=__continue/* EXTERNAL */){
        return _2M/*  sgOW */;
      }
    }
  };
  return new F(function(){return _2K/* sgOW */(_2J/* sgOU */, _/* EXTERNAL */);});
},
_2X/* disappearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_2Y/* toTab2 */ = function(_2Z/* sgPL */, _/* EXTERNAL */){
  while(1){
    var _30/* sgPN */ = E(_2Z/* sgPL */);
    if(!_30/* sgPN */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _31/* sgPS */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_30/* sgPN */.a), _/* EXTERNAL */));
      _2Z/* sgPL */ = _30/* sgPN */.b;
      continue;
    }
  }
},
_32/* toTab3 */ = function(_33/* sgPx */, _/* EXTERNAL */){
  var _34/* sgPz */ = E(_33/* sgPx */);
  if(!_34/* sgPz */._){
    return _k/* GHC.Types.[] */;
  }else{
    var _35/* sgPE */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
      return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_34/* sgPz */.a));
    },1))), _/* EXTERNAL */)),
    _36/* sgPH */ = B(_32/* FormEngine.FormElement.Tabs.toTab3 */(_34/* sgPz */.b, _/* EXTERNAL */));
    return new T2(1,_35/* sgPE */,_36/* sgPH */);
  }
},
_37/* toTab1 */ = function(_38/* sgPV */, _39/* sgPW */, _/* EXTERNAL */){
  var _3a/* sgQ0 */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
    return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_38/* sgPV */));
  },1))), _/* EXTERNAL */)),
  _3b/* sgQ3 */ = B(_32/* FormEngine.FormElement.Tabs.toTab3 */(_39/* sgPW */, _/* EXTERNAL */)),
  _3c/* sgQ6 */ = B(_2H/* FormEngine.FormElement.Tabs.colorizeTabs1 */(_38/* sgPV */, _39/* sgPW */, _/* EXTERNAL */)),
  _3d/* sgQ9 */ = B(_2Y/* FormEngine.FormElement.Tabs.toTab2 */(_3b/* sgQ3 */, _/* EXTERNAL */)),
  _3e/* sgQe */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, E(_3a/* sgQ0 */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_3f/* $wa */ = function(_3g/* sgQh */, _3h/* sgQi */, _3i/* sgQj */, _/* EXTERNAL */){
  var _3j/* sgQl */ = B(_X/* FormEngine.JQuery.$wa3 */(_1a/* FormEngine.FormElement.Tabs.lvl */, _3i/* sgQj */, _/* EXTERNAL */)),
  _3k/* sgQq */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
  _3l/* sgQt */ = __app1/* EXTERNAL */(_3k/* sgQq */, E(_3j/* sgQl */)),
  _3m/* sgQw */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
  _3n/* sgQz */ = __app1/* EXTERNAL */(_3m/* sgQw */, _3l/* sgQt */),
  _3o/* sgQC */ = B(_p/* FormEngine.JQuery.$wa */(_1b/* FormEngine.FormElement.Tabs.lvl1 */, _3n/* sgQz */, _/* EXTERNAL */)),
  _3p/* sgQF */ = function(_/* EXTERNAL */, _3q/* sgQH */){
    var _3r/* sgQN */ = __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_3q/* sgQH */)),
    _3s/* sgQQ */ = B(_X/* FormEngine.JQuery.$wa3 */(_1f/* FormEngine.FormElement.Tabs.lvl5 */, _3r/* sgQN */, _/* EXTERNAL */)),
    _3t/* sgQT */ = E(_3g/* sgQh */);
    if(!_3t/* sgQT */._){
      return _3s/* sgQQ */;
    }else{
      var _3u/* sgQW */ = E(_3h/* sgQi */);
      if(!_3u/* sgQW */._){
        return _3s/* sgQQ */;
      }else{
        var _3v/* sgQZ */ = B(A1(_3u/* sgQW */.a,_/* EXTERNAL */)),
        _3w/* sgR6 */ = E(_19/* FormEngine.JQuery.appendJq_f1 */),
        _3x/* sgR9 */ = __app2/* EXTERNAL */(_3w/* sgR6 */, E(_3v/* sgQZ */), E(_3s/* sgQQ */)),
        _3y/* sgRd */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
          return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_3t/* sgQT */.a));
        },1), _3x/* sgR9 */, _/* EXTERNAL */)),
        _3z/* sgRi */ = B(_P/* FormEngine.JQuery.$wa24 */(_1g/* FormEngine.FormElement.Tabs.lvl6 */, _1h/* FormEngine.FormElement.Tabs.lvl7 */, E(_3y/* sgRd */), _/* EXTERNAL */)),
        _3A/* sgRn */ = B(_C/* FormEngine.JQuery.$wa20 */(_1i/* FormEngine.FormElement.Tabs.lvl8 */, _1j/* FormEngine.FormElement.Tabs.lvl9 */, E(_3z/* sgRi */), _/* EXTERNAL */)),
        _3B/* sgRq */ = function(_3C/*  sgRr */, _3D/*  sgRs */, _3E/*  sgRt */, _/* EXTERNAL */){
          while(1){
            var _3F/*  sgRq */ = B((function(_3G/* sgRr */, _3H/* sgRs */, _3I/* sgRt */, _/* EXTERNAL */){
              var _3J/* sgRv */ = E(_3G/* sgRr */);
              if(!_3J/* sgRv */._){
                return _3I/* sgRt */;
              }else{
                var _3K/* sgRy */ = E(_3H/* sgRs */);
                if(!_3K/* sgRy */._){
                  return _3I/* sgRt */;
                }else{
                  var _3L/* sgRB */ = B(A1(_3K/* sgRy */.a,_/* EXTERNAL */)),
                  _3M/* sgRJ */ = __app2/* EXTERNAL */(_3w/* sgR6 */, E(_3L/* sgRB */), E(_3I/* sgRt */)),
                  _3N/* sgRN */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
                    return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_3J/* sgRv */.a));
                  },1), _3M/* sgRJ */, _/* EXTERNAL */)),
                  _3O/* sgRS */ = B(_P/* FormEngine.JQuery.$wa24 */(_1g/* FormEngine.FormElement.Tabs.lvl6 */, _1h/* FormEngine.FormElement.Tabs.lvl7 */, E(_3N/* sgRN */), _/* EXTERNAL */)),
                  _3P/* sgRX */ = B(_C/* FormEngine.JQuery.$wa20 */(_1i/* FormEngine.FormElement.Tabs.lvl8 */, _1j/* FormEngine.FormElement.Tabs.lvl9 */, E(_3O/* sgRS */), _/* EXTERNAL */));
                  _3C/*  sgRr */ = _3J/* sgRv */.b;
                  _3D/*  sgRs */ = _3K/* sgRy */.b;
                  _3E/*  sgRt */ = _3P/* sgRX */;
                  return __continue/* EXTERNAL */;
                }
              }
            })(_3C/*  sgRr */, _3D/*  sgRs */, _3E/*  sgRt */, _/* EXTERNAL */));
            if(_3F/*  sgRq */!=__continue/* EXTERNAL */){
              return _3F/*  sgRq */;
            }
          }
        };
        return new F(function(){return _3B/* sgRq */(_3t/* sgQT */.b, _3u/* sgQW */.b, _3A/* sgRn */, _/* EXTERNAL */);});
      }
    }
  },
  _3Q/* sgS0 */ = E(_3g/* sgQh */);
  if(!_3Q/* sgS0 */._){
    return new F(function(){return _3p/* sgQF */(_/* EXTERNAL */, _3o/* sgQC */);});
  }else{
    var _3R/* sgS1 */ = _3Q/* sgS0 */.a,
    _3S/* sgS5 */ = B(_X/* FormEngine.JQuery.$wa3 */(_1c/* FormEngine.FormElement.Tabs.lvl2 */, E(_3o/* sgQC */), _/* EXTERNAL */)),
    _3T/* sgSb */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
      return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_3R/* sgS1 */));
    },1), E(_3S/* sgS5 */), _/* EXTERNAL */)),
    _3U/* sgSh */ = __app1/* EXTERNAL */(_3k/* sgQq */, E(_3T/* sgSb */)),
    _3V/* sgSl */ = __app1/* EXTERNAL */(_3m/* sgQw */, _3U/* sgSh */),
    _3W/* sgSo */ = B(_X/* FormEngine.JQuery.$wa3 */(_1e/* FormEngine.FormElement.Tabs.lvl4 */, _3V/* sgSl */, _/* EXTERNAL */)),
    _3X/* sgSu */ = B(_1r/* FormEngine.JQuery.onClick1 */(function(_3Y/* sgSr */, _/* EXTERNAL */){
      return new F(function(){return _37/* FormEngine.FormElement.Tabs.toTab1 */(_3R/* sgS1 */, _3Q/* sgS0 */, _/* EXTERNAL */);});
    }, _3W/* sgSo */, _/* EXTERNAL */)),
    _3Z/* sgSA */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
      return B(_2i/* FormEngine.FormElement.Identifiers.tabName */(_3R/* sgS1 */));
    },1), E(_3X/* sgSu */), _/* EXTERNAL */)),
    _40/* sgSF */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
    _41/* sgSI */ = __app1/* EXTERNAL */(_40/* sgSF */, E(_3Z/* sgSA */)),
    _42/* sgSL */ = function(_43/*  sgSM */, _44/*  sgSN */, _45/*  sgKJ */, _/* EXTERNAL */){
      while(1){
        var _46/*  sgSL */ = B((function(_47/* sgSM */, _48/* sgSN */, _49/* sgKJ */, _/* EXTERNAL */){
          var _4a/* sgSP */ = E(_47/* sgSM */);
          if(!_4a/* sgSP */._){
            return _48/* sgSN */;
          }else{
            var _4b/* sgSR */ = _4a/* sgSP */.a,
            _4c/* sgST */ = B(_X/* FormEngine.JQuery.$wa3 */(_1c/* FormEngine.FormElement.Tabs.lvl2 */, _48/* sgSN */, _/* EXTERNAL */)),
            _4d/* sgSZ */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
              return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_4b/* sgSR */));
            },1), E(_4c/* sgST */), _/* EXTERNAL */)),
            _4e/* sgT5 */ = __app1/* EXTERNAL */(_3k/* sgQq */, E(_4d/* sgSZ */)),
            _4f/* sgT9 */ = __app1/* EXTERNAL */(_3m/* sgQw */, _4e/* sgT5 */),
            _4g/* sgTc */ = B(_X/* FormEngine.JQuery.$wa3 */(_1e/* FormEngine.FormElement.Tabs.lvl4 */, _4f/* sgT9 */, _/* EXTERNAL */)),
            _4h/* sgTi */ = B(_1r/* FormEngine.JQuery.onClick1 */(function(_4i/* sgTf */, _/* EXTERNAL */){
              return new F(function(){return _37/* FormEngine.FormElement.Tabs.toTab1 */(_4b/* sgSR */, _3Q/* sgS0 */, _/* EXTERNAL */);});
            }, _4g/* sgTc */, _/* EXTERNAL */)),
            _4j/* sgTo */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
              return B(_2i/* FormEngine.FormElement.Identifiers.tabName */(_4b/* sgSR */));
            },1), E(_4h/* sgTi */), _/* EXTERNAL */)),
            _4k/* sgTu */ = __app1/* EXTERNAL */(_40/* sgSF */, E(_4j/* sgTo */)),
            _4l/*   sgKJ */ = _/* EXTERNAL */;
            _43/*  sgSM */ = _4a/* sgSP */.b;
            _44/*  sgSN */ = _4k/* sgTu */;
            _45/*  sgKJ */ = _4l/*   sgKJ */;
            return __continue/* EXTERNAL */;
          }
        })(_43/*  sgSM */, _44/*  sgSN */, _45/*  sgKJ */, _/* EXTERNAL */));
        if(_46/*  sgSL */!=__continue/* EXTERNAL */){
          return _46/*  sgSL */;
        }
      }
    },
    _4m/* sgTx */ = B(_42/* sgSL */(_3Q/* sgS0 */.b, _41/* sgSI */, _/* EXTERNAL */, _/* EXTERNAL */));
    return new F(function(){return _3p/* sgQF */(_/* EXTERNAL */, _4m/* sgTx */);});
  }
},
_4n/* mouseleave2 */ = "(function (jq) { jq.mouseleave(); })",
_4o/* $wa14 */ = function(_4p/* sjVx */, _/* EXTERNAL */){
  var _4q/* sjVC */ = eval/* EXTERNAL */(E(_4n/* FormEngine.JQuery.mouseleave2 */)),
  _4r/* sjVK */ = __app1/* EXTERNAL */(E(_4q/* sjVC */), _4p/* sjVx */);
  return _4p/* sjVx */;
},
_4s/* click2 */ = "(function (jq) { jq.click(); })",
_4t/* $wa5 */ = function(_4u/* sjWH */, _/* EXTERNAL */){
  var _4v/* sjWM */ = eval/* EXTERNAL */(E(_4s/* FormEngine.JQuery.click2 */)),
  _4w/* sjWU */ = __app1/* EXTERNAL */(E(_4v/* sjWM */), _4u/* sjWH */);
  return _4u/* sjWH */;
},
_4x/* False */ = false,
_4y/* Nothing */ = __Z/* EXTERNAL */,
_4z/* aboutTab4 */ = 0,
_4A/* aboutTab6 */ = 1000,
_4B/* aboutTab5 */ = new T2(1,_4A/* Form.aboutTab6 */,_k/* GHC.Types.[] */),
_4C/* aboutTab3 */ = new T2(1,_4B/* Form.aboutTab5 */,_4z/* Form.aboutTab4 */),
_4D/* aboutTab8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("About"));
}),
_4E/* aboutTab7 */ = new T1(1,_4D/* Form.aboutTab8 */),
_4F/* aboutTab2 */ = {_:0,a:_4E/* Form.aboutTab7 */,b:_4C/* Form.aboutTab3 */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_4y/* GHC.Base.Nothing */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_4G/* aboutTab1 */ = new T2(6,_4F/* Form.aboutTab2 */,_k/* GHC.Types.[] */),
_4H/* aboutTab */ = new T3(0,_4G/* Form.aboutTab1 */,_k/* GHC.Types.[] */,_4x/* GHC.Types.False */),
_4I/* aboutTabPaneJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("  <div>    <p>      Questionnaire generated from precompiler JSON of <a href=\"https://github.com/CCMi-FIT/ds-km\" target=\"_blank\">Data Stewardship Knowledge Model</a>.    </p>  </div> "));
}),
_4J/* aboutTabPaneJq1 */ = function(_/* EXTERNAL */){
  return new F(function(){return _2E/* FormEngine.JQuery.select1 */(_4I/* Form.aboutTabPaneJq2 */, _/* EXTERNAL */);});
},
_4K/* descSubpaneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane"));
}),
_4L/* elemChapter */ = function(_4M/* sbVq */){
  while(1){
    var _4N/* sbVr */ = E(_4M/* sbVq */);
    switch(_4N/* sbVr */._){
      case 0:
        return E(_4N/* sbVr */);
      case 1:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 2:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 3:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 4:
        _4M/* sbVq */ = _4N/* sbVr */.d;
        continue;
      case 5:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 6:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 7:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 8:
        _4M/* sbVq */ = _4N/* sbVr */.d;
        continue;
      case 9:
        _4M/* sbVq */ = _4N/* sbVr */.c;
        continue;
      case 10:
        _4M/* sbVq */ = _4N/* sbVr */.b;
        continue;
      default:
        _4M/* sbVq */ = _4N/* sbVr */.b;
        continue;
    }
  }
},
_4O/* descSubpaneId */ = function(_4P/* sfrC */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(B(_4L/* FormEngine.FormElement.FormElement.elemChapter */(_4P/* sfrC */)))))).b)), _4K/* FormEngine.FormElement.Identifiers.descSubpaneId1 */);});
},
_4Q/* descSubpaneParagraphId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane-text"));
}),
_4R/* descSubpaneParagraphId */ = function(_4S/* sfu3 */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(B(_4L/* FormEngine.FormElement.FormElement.elemChapter */(_4S/* sfu3 */)))))).b)), _4Q/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */);});
},
_4T/* $fEqOption_$c== */ = function(_4U/* s52z */, _4V/* s52A */){
  var _4W/* s52B */ = E(_4U/* s52z */);
  if(!_4W/* s52B */._){
    var _4X/* s52C */ = _4W/* s52B */.a,
    _4Y/* s52D */ = E(_4V/* s52A */);
    if(!_4Y/* s52D */._){
      return new F(function(){return _2n/* GHC.Base.eqString */(_4X/* s52C */, _4Y/* s52D */.a);});
    }else{
      return new F(function(){return _2n/* GHC.Base.eqString */(_4X/* s52C */, _4Y/* s52D */.b);});
    }
  }else{
    var _4Z/* s52J */ = _4W/* s52B */.b,
    _50/* s52L */ = E(_4V/* s52A */);
    if(!_50/* s52L */._){
      return new F(function(){return _2n/* GHC.Base.eqString */(_4Z/* s52J */, _50/* s52L */.a);});
    }else{
      return new F(function(){return _2n/* GHC.Base.eqString */(_4Z/* s52J */, _50/* s52L */.b);});
    }
  }
},
_51/* $fShowNumbering2 */ = 0,
_52/* $fShowFormElement1 */ = function(_53/* sbPd */, _54/* sbPe */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_55/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_53/* sbPd */)), _54/* sbPe */);});
},
_56/* $fShowMaybe1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just "));
}),
_57/* $fShowMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_58/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SubmitButtonElem id="));
}),
_59/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SaveButtonElem id="));
}),
_5a/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NumberElem id="));
}),
_5b/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EmailElem id="));
}),
_5c/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TextElem id="));
}),
_5d/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("StringElem id="));
}),
_5e/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChapterElem id="));
}),
_5f/* shows5 */ = 34,
_5g/* lvl15 */ = new T2(1,_5f/* GHC.Show.shows5 */,_k/* GHC.Types.[] */),
_5h/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElem id="));
}),
_5i/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" children: "));
}),
_5j/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OptionalGroupElem id="));
}),
_5k/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SimpleGroupElem id="));
}),
_5l/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" value="));
}),
_5m/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ListElem id="));
}),
_5n/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChoiceElem id="));
}),
_5o/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" unit="));
}),
_5p/* showList__1 */ = 44,
_5q/* showList__2 */ = 93,
_5r/* showList__3 */ = 91,
_5s/* showList__ */ = function(_5t/* sfc2 */, _5u/* sfc3 */, _5v/* sfc4 */){
  var _5w/* sfc5 */ = E(_5u/* sfc3 */);
  if(!_5w/* sfc5 */._){
    return new F(function(){return unAppCStr/* EXTERNAL */("[]", _5v/* sfc4 */);});
  }else{
    var _5x/* sfch */ = new T(function(){
      var _5y/* sfcg */ = new T(function(){
        var _5z/* sfc9 */ = function(_5A/* sfca */){
          var _5B/* sfcb */ = E(_5A/* sfca */);
          if(!_5B/* sfcb */._){
            return E(new T2(1,_5q/* GHC.Show.showList__2 */,_5v/* sfc4 */));
          }else{
            var _5C/* sfcf */ = new T(function(){
              return B(A2(_5t/* sfc2 */,_5B/* sfcb */.a, new T(function(){
                return B(_5z/* sfc9 */(_5B/* sfcb */.b));
              })));
            });
            return new T2(1,_5p/* GHC.Show.showList__1 */,_5C/* sfcf */);
          }
        };
        return B(_5z/* sfc9 */(_5w/* sfc5 */.b));
      });
      return B(A2(_5t/* sfc2 */,_5w/* sfc5 */.a, _5y/* sfcg */));
    });
    return new T2(1,_5r/* GHC.Show.showList__3 */,_5x/* sfch */);
  }
},
_5D/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_5E/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_5F/* lvl2 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_5E/* GHC.List.prel_list_str */, _5D/* GHC.List.lvl1 */));
}),
_5G/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_5F/* GHC.List.lvl2 */));
}),
_5H/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_5I/* lvl4 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_5E/* GHC.List.prel_list_str */, _5H/* GHC.List.lvl3 */));
}),
_5J/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_5I/* GHC.List.lvl4 */));
}),
_5K/* poly_$wgo2 */ = function(_5L/* s9uh */, _5M/* s9ui */){
  while(1){
    var _5N/* s9uj */ = E(_5L/* s9uh */);
    if(!_5N/* s9uj */._){
      return E(_5J/* GHC.List.!!1 */);
    }else{
      var _5O/* s9um */ = E(_5M/* s9ui */);
      if(!_5O/* s9um */){
        return E(_5N/* s9uj */.a);
      }else{
        _5L/* s9uh */ = _5N/* s9uj */.b;
        _5M/* s9ui */ = _5O/* s9um */-1|0;
        continue;
      }
    }
  }
},
_5P/* $w!! */ = function(_5Q/* s9uo */, _5R/* s9up */){
  if(_5R/* s9up */>=0){
    return new F(function(){return _5K/* GHC.List.poly_$wgo2 */(_5Q/* s9uo */, _5R/* s9up */);});
  }else{
    return E(_5G/* GHC.List.negIndex */);
  }
},
_5S/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_5T/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_5U/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_5V/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_5W/* asciiTab32 */ = new T2(1,_5V/* GHC.Show.asciiTab33 */,_k/* GHC.Types.[] */),
_5X/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_5Y/* asciiTab31 */ = new T2(1,_5X/* GHC.Show.asciiTab34 */,_5W/* GHC.Show.asciiTab32 */),
_5Z/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_60/* asciiTab30 */ = new T2(1,_5Z/* GHC.Show.asciiTab35 */,_5Y/* GHC.Show.asciiTab31 */),
_61/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_62/* asciiTab29 */ = new T2(1,_61/* GHC.Show.asciiTab36 */,_60/* GHC.Show.asciiTab30 */),
_63/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_64/* asciiTab28 */ = new T2(1,_63/* GHC.Show.asciiTab37 */,_62/* GHC.Show.asciiTab29 */),
_65/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_66/* asciiTab27 */ = new T2(1,_65/* GHC.Show.asciiTab38 */,_64/* GHC.Show.asciiTab28 */),
_67/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_68/* asciiTab26 */ = new T2(1,_67/* GHC.Show.asciiTab39 */,_66/* GHC.Show.asciiTab27 */),
_69/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_6a/* asciiTab25 */ = new T2(1,_69/* GHC.Show.asciiTab40 */,_68/* GHC.Show.asciiTab26 */),
_6b/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_6c/* asciiTab24 */ = new T2(1,_6b/* GHC.Show.asciiTab41 */,_6a/* GHC.Show.asciiTab25 */),
_6d/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_6e/* asciiTab23 */ = new T2(1,_6d/* GHC.Show.asciiTab42 */,_6c/* GHC.Show.asciiTab24 */),
_6f/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_6g/* asciiTab22 */ = new T2(1,_6f/* GHC.Show.asciiTab43 */,_6e/* GHC.Show.asciiTab23 */),
_6h/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_6i/* asciiTab21 */ = new T2(1,_6h/* GHC.Show.asciiTab44 */,_6g/* GHC.Show.asciiTab22 */),
_6j/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_6k/* asciiTab20 */ = new T2(1,_6j/* GHC.Show.asciiTab45 */,_6i/* GHC.Show.asciiTab21 */),
_6l/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_6m/* asciiTab19 */ = new T2(1,_6l/* GHC.Show.asciiTab46 */,_6k/* GHC.Show.asciiTab20 */),
_6n/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_6o/* asciiTab18 */ = new T2(1,_6n/* GHC.Show.asciiTab47 */,_6m/* GHC.Show.asciiTab19 */),
_6p/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_6q/* asciiTab17 */ = new T2(1,_6p/* GHC.Show.asciiTab48 */,_6o/* GHC.Show.asciiTab18 */),
_6r/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_6s/* asciiTab16 */ = new T2(1,_6r/* GHC.Show.asciiTab49 */,_6q/* GHC.Show.asciiTab17 */),
_6t/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_6u/* asciiTab15 */ = new T2(1,_6t/* GHC.Show.asciiTab50 */,_6s/* GHC.Show.asciiTab16 */),
_6v/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_6w/* asciiTab14 */ = new T2(1,_6v/* GHC.Show.asciiTab51 */,_6u/* GHC.Show.asciiTab15 */),
_6x/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_6y/* asciiTab13 */ = new T2(1,_6x/* GHC.Show.asciiTab52 */,_6w/* GHC.Show.asciiTab14 */),
_6z/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_6A/* asciiTab12 */ = new T2(1,_6z/* GHC.Show.asciiTab53 */,_6y/* GHC.Show.asciiTab13 */),
_6B/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_6C/* asciiTab11 */ = new T2(1,_6B/* GHC.Show.asciiTab54 */,_6A/* GHC.Show.asciiTab12 */),
_6D/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_6E/* asciiTab10 */ = new T2(1,_6D/* GHC.Show.asciiTab55 */,_6C/* GHC.Show.asciiTab11 */),
_6F/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_6G/* asciiTab9 */ = new T2(1,_6F/* GHC.Show.asciiTab56 */,_6E/* GHC.Show.asciiTab10 */),
_6H/* asciiTab8 */ = new T2(1,_5U/* GHC.Show.asciiTab57 */,_6G/* GHC.Show.asciiTab9 */),
_6I/* asciiTab7 */ = new T2(1,_5T/* GHC.Show.asciiTab58 */,_6H/* GHC.Show.asciiTab8 */),
_6J/* asciiTab6 */ = new T2(1,_5S/* GHC.Show.asciiTab59 */,_6I/* GHC.Show.asciiTab7 */),
_6K/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_6L/* asciiTab5 */ = new T2(1,_6K/* GHC.Show.asciiTab60 */,_6J/* GHC.Show.asciiTab6 */),
_6M/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_6N/* asciiTab4 */ = new T2(1,_6M/* GHC.Show.asciiTab61 */,_6L/* GHC.Show.asciiTab5 */),
_6O/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_6P/* asciiTab3 */ = new T2(1,_6O/* GHC.Show.asciiTab62 */,_6N/* GHC.Show.asciiTab4 */),
_6Q/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_6R/* asciiTab2 */ = new T2(1,_6Q/* GHC.Show.asciiTab63 */,_6P/* GHC.Show.asciiTab3 */),
_6S/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_6T/* asciiTab1 */ = new T2(1,_6S/* GHC.Show.asciiTab64 */,_6R/* GHC.Show.asciiTab2 */),
_6U/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_6V/* asciiTab */ = new T2(1,_6U/* GHC.Show.asciiTab65 */,_6T/* GHC.Show.asciiTab1 */),
_6W/* lvl */ = 92,
_6X/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_6Y/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_6Z/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_70/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_71/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_72/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_73/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_74/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_75/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_76/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_77/* $wshowLitChar */ = function(_78/* sfeh */, _79/* sfei */){
  if(_78/* sfeh */<=127){
    var _7a/* sfel */ = E(_78/* sfeh */);
    switch(_7a/* sfel */){
      case 92:
        return new F(function(){return _7/* GHC.Base.++ */(_6Z/* GHC.Show.lvl2 */, _79/* sfei */);});
        break;
      case 127:
        return new F(function(){return _7/* GHC.Base.++ */(_6X/* GHC.Show.lvl1 */, _79/* sfei */);});
        break;
      default:
        if(_7a/* sfel */<32){
          var _7b/* sfeo */ = E(_7a/* sfel */);
          switch(_7b/* sfeo */){
            case 7:
              return new F(function(){return _7/* GHC.Base.++ */(_6Y/* GHC.Show.lvl10 */, _79/* sfei */);});
              break;
            case 8:
              return new F(function(){return _7/* GHC.Base.++ */(_76/* GHC.Show.lvl9 */, _79/* sfei */);});
              break;
            case 9:
              return new F(function(){return _7/* GHC.Base.++ */(_75/* GHC.Show.lvl8 */, _79/* sfei */);});
              break;
            case 10:
              return new F(function(){return _7/* GHC.Base.++ */(_74/* GHC.Show.lvl7 */, _79/* sfei */);});
              break;
            case 11:
              return new F(function(){return _7/* GHC.Base.++ */(_73/* GHC.Show.lvl6 */, _79/* sfei */);});
              break;
            case 12:
              return new F(function(){return _7/* GHC.Base.++ */(_72/* GHC.Show.lvl5 */, _79/* sfei */);});
              break;
            case 13:
              return new F(function(){return _7/* GHC.Base.++ */(_71/* GHC.Show.lvl4 */, _79/* sfei */);});
              break;
            case 14:
              return new F(function(){return _7/* GHC.Base.++ */(_70/* GHC.Show.lvl3 */, new T(function(){
                var _7c/* sfes */ = E(_79/* sfei */);
                if(!_7c/* sfes */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_7c/* sfes */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _7c/* sfes */));
                  }else{
                    return E(_7c/* sfes */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _7/* GHC.Base.++ */(new T2(1,_6W/* GHC.Show.lvl */,new T(function(){
                return B(_5P/* GHC.List.$w!! */(_6V/* GHC.Show.asciiTab */, _7b/* sfeo */));
              })), _79/* sfei */);});
          }
        }else{
          return new T2(1,_7a/* sfel */,_79/* sfei */);
        }
    }
  }else{
    var _7d/* sfeR */ = new T(function(){
      var _7e/* sfeC */ = jsShowI/* EXTERNAL */(_78/* sfeh */);
      return B(_7/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_7e/* sfeC */), new T(function(){
        var _7f/* sfeH */ = E(_79/* sfei */);
        if(!_7f/* sfeH */._){
          return __Z/* EXTERNAL */;
        }else{
          var _7g/* sfeK */ = E(_7f/* sfeH */.a);
          if(_7g/* sfeK */<48){
            return E(_7f/* sfeH */);
          }else{
            if(_7g/* sfeK */>57){
              return E(_7f/* sfeH */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _7f/* sfeH */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_6W/* GHC.Show.lvl */,_7d/* sfeR */);
  }
},
_7h/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_7i/* showLitString */ = function(_7j/* sfeW */, _7k/* sfeX */){
  var _7l/* sfeY */ = E(_7j/* sfeW */);
  if(!_7l/* sfeY */._){
    return E(_7k/* sfeX */);
  }else{
    var _7m/* sff0 */ = _7l/* sfeY */.b,
    _7n/* sff3 */ = E(_7l/* sfeY */.a);
    if(_7n/* sff3 */==34){
      return new F(function(){return _7/* GHC.Base.++ */(_7h/* GHC.Show.lvl11 */, new T(function(){
        return B(_7i/* GHC.Show.showLitString */(_7m/* sff0 */, _7k/* sfeX */));
      },1));});
    }else{
      return new F(function(){return _77/* GHC.Show.$wshowLitChar */(_7n/* sff3 */, new T(function(){
        return B(_7i/* GHC.Show.showLitString */(_7m/* sff0 */, _7k/* sfeX */));
      }));});
    }
  }
},
_55/* $fShowFormElement_$cshow */ = function(_7o/* sbPg */){
  var _7p/* sbPh */ = E(_7o/* sbPg */);
  switch(_7p/* sbPh */._){
    case 0:
      var _7q/* sbPA */ = new T(function(){
        var _7r/* sbPz */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_5i/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_5s/* GHC.Show.showList__ */(_52/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _7p/* sbPh */.b, _k/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), _7r/* sbPz */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5e/* FormEngine.FormElement.FormElement.lvl14 */, _7q/* sbPA */);});
      break;
    case 1:
      var _7s/* sbPS */ = new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), new T(function(){
          return B(_7/* GHC.Base.++ */(_5l/* FormEngine.FormElement.FormElement.lvl6 */, _7p/* sbPh */.b));
        },1)));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5d/* FormEngine.FormElement.FormElement.lvl13 */, _7s/* sbPS */);});
      break;
    case 2:
      var _7t/* sbQa */ = new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), new T(function(){
          return B(_7/* GHC.Base.++ */(_5l/* FormEngine.FormElement.FormElement.lvl6 */, _7p/* sbPh */.b));
        },1)));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5c/* FormEngine.FormElement.FormElement.lvl12 */, _7t/* sbQa */);});
      break;
    case 3:
      var _7u/* sbQs */ = new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), new T(function(){
          return B(_7/* GHC.Base.++ */(_5l/* FormEngine.FormElement.FormElement.lvl6 */, _7p/* sbPh */.b));
        },1)));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5b/* FormEngine.FormElement.FormElement.lvl11 */, _7u/* sbQs */);});
      break;
    case 4:
      var _7v/* sbQY */ = new T(function(){
        var _7w/* sbQX */ = new T(function(){
          var _7x/* sbQW */ = new T(function(){
            var _7y/* sbQK */ = new T(function(){
              var _7z/* sbQP */ = new T(function(){
                var _7A/* sbQL */ = E(_7p/* sbPh */.c);
                if(!_7A/* sbQL */._){
                  return E(_57/* GHC.Show.$fShowMaybe3 */);
                }else{
                  return B(_7/* GHC.Base.++ */(_56/* GHC.Show.$fShowMaybe1 */, new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
                    return B(_7i/* GHC.Show.showLitString */(_7A/* sbQL */.a, _5g/* FormEngine.FormElement.FormElement.lvl15 */));
                  }))));
                }
              },1);
              return B(_7/* GHC.Base.++ */(_5o/* FormEngine.FormElement.FormElement.lvl9 */, _7z/* sbQP */));
            }),
            _7B/* sbQQ */ = E(_7p/* sbPh */.b);
            if(!_7B/* sbQQ */._){
              return B(_7/* GHC.Base.++ */(_57/* GHC.Show.$fShowMaybe3 */, _7y/* sbQK */));
            }else{
              return B(_7/* GHC.Base.++ */(_56/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_7/* GHC.Base.++ */(B(_1M/* GHC.Show.$wshowSignedInt */(11, E(_7B/* sbQQ */.a), _k/* GHC.Types.[] */)), _7y/* sbQK */));
              },1)));
            }
          },1);
          return B(_7/* GHC.Base.++ */(_5l/* FormEngine.FormElement.FormElement.lvl6 */, _7x/* sbQW */));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), _7w/* sbQX */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5a/* FormEngine.FormElement.FormElement.lvl10 */, _7v/* sbQY */);});
      break;
    case 5:
      return new F(function(){return _7/* GHC.Base.++ */(_5n/* FormEngine.FormElement.FormElement.lvl8 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b));
      },1));});
      break;
    case 6:
      var _7C/* sbRB */ = new T(function(){
        var _7D/* sbRA */ = new T(function(){
          var _7E/* sbRz */ = new T(function(){
            var _7F/* sbRv */ = E(_7p/* sbPh */.b);
            if(!_7F/* sbRv */._){
              return E(_57/* GHC.Show.$fShowMaybe3 */);
            }else{
              return B(_7/* GHC.Base.++ */(_56/* GHC.Show.$fShowMaybe1 */, new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
                return B(_7i/* GHC.Show.showLitString */(_7F/* sbRv */.a, _5g/* FormEngine.FormElement.FormElement.lvl15 */));
              }))));
            }
          },1);
          return B(_7/* GHC.Base.++ */(_5l/* FormEngine.FormElement.FormElement.lvl6 */, _7E/* sbRz */));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), _7D/* sbRA */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5m/* FormEngine.FormElement.FormElement.lvl7 */, _7C/* sbRB */);});
      break;
    case 7:
      var _7G/* sbRU */ = new T(function(){
        var _7H/* sbRT */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_5i/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_5s/* GHC.Show.showList__ */(_52/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _7p/* sbPh */.b, _k/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), _7H/* sbRT */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5k/* FormEngine.FormElement.FormElement.lvl5 */, _7G/* sbRU */);});
      break;
    case 8:
      var _7I/* sbSe */ = new T(function(){
        var _7J/* sbSd */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_5i/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_5s/* GHC.Show.showList__ */(_52/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _7p/* sbPh */.c, _k/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b)), _7J/* sbSd */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5j/* FormEngine.FormElement.FormElement.lvl4 */, _7I/* sbSe */);});
      break;
    case 9:
      return new F(function(){return _7/* GHC.Base.++ */(_5h/* FormEngine.FormElement.FormElement.lvl2 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b));
      },1));});
      break;
    case 10:
      return new F(function(){return _7/* GHC.Base.++ */(_59/* FormEngine.FormElement.FormElement.lvl1 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b));
      },1));});
      break;
    default:
      return new F(function(){return _7/* GHC.Base.++ */(_58/* FormEngine.FormElement.FormElement.lvl */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7p/* sbPh */.a)).b));
      },1));});
  }
},
_7K/* lvl56 */ = new T2(1,_5f/* GHC.Show.shows5 */,_k/* GHC.Types.[] */),
_7L/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IntValueRule (Int -> Bool)"));
}),
_7M/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ReadOnlyRule"));
}),
_7N/* shows_$cshowList */ = function(_7O/* sff6 */, _7P/* sff7 */){
  return new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
    return B(_7i/* GHC.Show.showLitString */(_7O/* sff6 */, new T2(1,_5f/* GHC.Show.shows5 */,_7P/* sff7 */)));
  }));
},
_7Q/* $fShowFormRule_$cshow */ = function(_7R/* s51R */){
  var _7S/* s51S */ = E(_7R/* s51R */);
  switch(_7S/* s51S */._){
    case 0:
      var _7T/* s51Z */ = new T(function(){
        var _7U/* s51Y */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
            return B(_7i/* GHC.Show.showLitString */(_7S/* s51S */.b, _7K/* FormEngine.FormItem.lvl56 */));
          }))));
        },1);
        return B(_7/* GHC.Base.++ */(B(_5s/* GHC.Show.showList__ */(_7N/* GHC.Show.shows_$cshowList */, _7S/* s51S */.a, _k/* GHC.Types.[] */)), _7U/* s51Y */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumRule @ ", _7T/* s51Z */);});
      break;
    case 1:
      var _7V/* s526 */ = new T(function(){
        var _7W/* s525 */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
            return B(_7i/* GHC.Show.showLitString */(_7S/* s51S */.b, _7K/* FormEngine.FormItem.lvl56 */));
          }))));
        },1);
        return B(_7/* GHC.Base.++ */(B(_5s/* GHC.Show.showList__ */(_7N/* GHC.Show.shows_$cshowList */, _7S/* s51S */.a, _k/* GHC.Types.[] */)), _7W/* s525 */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumTBsRule @ ", _7V/* s526 */);});
      break;
    case 2:
      var _7X/* s52e */ = new T(function(){
        var _7Y/* s52d */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
            return B(_7i/* GHC.Show.showLitString */(_7S/* s51S */.b, _7K/* FormEngine.FormItem.lvl56 */));
          }))));
        },1);
        return B(_7/* GHC.Base.++ */(new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
          return B(_7i/* GHC.Show.showLitString */(_7S/* s51S */.a, _7K/* FormEngine.FormItem.lvl56 */));
        })), _7Y/* s52d */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("CopyValueRule @ ", _7X/* s52e */);});
      break;
    case 3:
      return E(_7M/* FormEngine.FormItem.lvl7 */);
    default:
      return E(_7L/* FormEngine.FormItem.lvl6 */);
  }
},
_7Z/* identity2element' */ = function(_80/* siZS */, _81/* siZT */){
  var _82/* siZU */ = E(_81/* siZT */);
  if(!_82/* siZU */._){
    return __Z/* EXTERNAL */;
  }else{
    var _83/* siZV */ = _82/* siZU */.a,
    _84/* sj0a */ = function(_85/* sj0b */){
      var _86/* sj0d */ = B(_7Z/* FormEngine.FormElement.Updating.identity2element' */(_80/* siZS */, B(_l/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_83/* siZV */))));
      if(!_86/* sj0d */._){
        return new F(function(){return _7Z/* FormEngine.FormElement.Updating.identity2element' */(_80/* siZS */, _82/* siZU */.b);});
      }else{
        return E(_86/* sj0d */);
      }
    },
    _87/* sj0f */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_83/* siZV */)))).c);
    if(!_87/* sj0f */._){
      if(!B(_2n/* GHC.Base.eqString */(_k/* GHC.Types.[] */, _80/* siZS */))){
        return new F(function(){return _84/* sj0a */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_83/* siZV */);
      }
    }else{
      if(!B(_2n/* GHC.Base.eqString */(_87/* sj0f */.a, _80/* siZS */))){
        return new F(function(){return _84/* sj0a */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_83/* siZV */);
      }
    }
  }
},
_88/* getRadioValue2 */ = "(function (elId) { return $(elId); })",
_89/* getRadioValue3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\']:checked"));
}),
_8a/* getRadioValue4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("[name=\'"));
}),
_8b/* getRadioValue_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.val(); })");
}),
_8c/* getRadioValue1 */ = function(_8d/* skbp */, _/* EXTERNAL */){
  var _8e/* skbA */ = eval/* EXTERNAL */(E(_88/* FormEngine.JQuery.getRadioValue2 */)),
  _8f/* skbI */ = __app1/* EXTERNAL */(E(_8e/* skbA */), toJSStr/* EXTERNAL */(B(_7/* GHC.Base.++ */(_8a/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_7/* GHC.Base.++ */(_8d/* skbp */, _89/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _8g/* skbO */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), _8f/* skbI */);
  return new T(function(){
    var _8h/* skbS */ = String/* EXTERNAL */(_8g/* skbO */);
    return fromJSStr/* EXTERNAL */(_8h/* skbS */);
  });
},
_8i/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("undefined"));
}),
_8j/* nfiUnitId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_unit"));
}),
_8k/* readEither6 */ = function(_8l/*  s2Rf3 */){
  while(1){
    var _8m/*  readEither6 */ = B((function(_8n/* s2Rf3 */){
      var _8o/* s2Rf4 */ = E(_8n/* s2Rf3 */);
      if(!_8o/* s2Rf4 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _8p/* s2Rf6 */ = _8o/* s2Rf4 */.b,
        _8q/* s2Rf7 */ = E(_8o/* s2Rf4 */.a);
        if(!E(_8q/* s2Rf7 */.b)._){
          return new T2(1,_8q/* s2Rf7 */.a,new T(function(){
            return B(_8k/* Text.Read.readEither6 */(_8p/* s2Rf6 */));
          }));
        }else{
          _8l/*  s2Rf3 */ = _8p/* s2Rf6 */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_8l/*  s2Rf3 */));
    if(_8m/*  readEither6 */!=__continue/* EXTERNAL */){
      return _8m/*  readEither6 */;
    }
  }
},
_8r/* run */ = function(_8s/*  s1iAI */, _8t/*  s1iAJ */){
  while(1){
    var _8u/*  run */ = B((function(_8v/* s1iAI */, _8w/* s1iAJ */){
      var _8x/* s1iAK */ = E(_8v/* s1iAI */);
      switch(_8x/* s1iAK */._){
        case 0:
          var _8y/* s1iAM */ = E(_8w/* s1iAJ */);
          if(!_8y/* s1iAM */._){
            return __Z/* EXTERNAL */;
          }else{
            _8s/*  s1iAI */ = B(A1(_8x/* s1iAK */.a,_8y/* s1iAM */.a));
            _8t/*  s1iAJ */ = _8y/* s1iAM */.b;
            return __continue/* EXTERNAL */;
          }
          break;
        case 1:
          var _8z/*   s1iAI */ = B(A1(_8x/* s1iAK */.a,_8w/* s1iAJ */)),
          _8A/*   s1iAJ */ = _8w/* s1iAJ */;
          _8s/*  s1iAI */ = _8z/*   s1iAI */;
          _8t/*  s1iAJ */ = _8A/*   s1iAJ */;
          return __continue/* EXTERNAL */;
        case 2:
          return __Z/* EXTERNAL */;
        case 3:
          return new T2(1,new T2(0,_8x/* s1iAK */.a,_8w/* s1iAJ */),new T(function(){
            return B(_8r/* Text.ParserCombinators.ReadP.run */(_8x/* s1iAK */.b, _8w/* s1iAJ */));
          }));
        default:
          return E(_8x/* s1iAK */.a);
      }
    })(_8s/*  s1iAI */, _8t/*  s1iAJ */));
    if(_8u/*  run */!=__continue/* EXTERNAL */){
      return _8u/*  run */;
    }
  }
},
_8B/* selectByName2 */ = "(function (name) { return $(\'[name=\"\' + name + \'\"]\'); })",
_8C/* selectByName1 */ = function(_8D/* sk8L */, _/* EXTERNAL */){
  var _8E/* sk8V */ = eval/* EXTERNAL */(E(_8B/* FormEngine.JQuery.selectByName2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_8E/* sk8V */), toJSStr/* EXTERNAL */(E(_8D/* sk8L */)));});
},
_8F/* True */ = true,
_8G/* map */ = function(_8H/* s3ht */, _8I/* s3hu */){
  var _8J/* s3hv */ = E(_8I/* s3hu */);
  return (_8J/* s3hv */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T(function(){
    return B(A1(_8H/* s3ht */,_8J/* s3hv */.a));
  }),new T(function(){
    return B(_8G/* GHC.Base.map */(_8H/* s3ht */, _8J/* s3hv */.b));
  }));
},
_8K/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_8L/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_8M/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_8N/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_8K/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_8L/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_8M/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_8O/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_8N/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */),
_8P/* $fExceptionPatternMatchFail1 */ = function(_8Q/* s4nv1 */){
  return E(_8O/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_8R/* $p1Exception */ = function(_8S/* s2Szo */){
  return E(E(_8S/* s2Szo */).a);
},
_8T/* cast */ = function(_8U/* s26is */, _8V/* s26it */, _8W/* s26iu */){
  var _8X/* s26iv */ = B(A1(_8U/* s26is */,_/* EXTERNAL */)),
  _8Y/* s26iB */ = B(A1(_8V/* s26it */,_/* EXTERNAL */)),
  _8Z/* s26iI */ = hs_eqWord64/* EXTERNAL */(_8X/* s26iv */.a, _8Y/* s26iB */.a);
  if(!_8Z/* s26iI */){
    return __Z/* EXTERNAL */;
  }else{
    var _90/* s26iN */ = hs_eqWord64/* EXTERNAL */(_8X/* s26iv */.b, _8Y/* s26iB */.b);
    return (!_90/* s26iN */) ? __Z/* EXTERNAL */ : new T1(1,_8W/* s26iu */);
  }
},
_91/* $fExceptionPatternMatchFail_$cfromException */ = function(_92/* s4nvc */){
  var _93/* s4nvd */ = E(_92/* s4nvc */);
  return new F(function(){return _8T/* Data.Typeable.cast */(B(_8R/* GHC.Exception.$p1Exception */(_93/* s4nvd */.a)), _8P/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _93/* s4nvd */.b);});
},
_94/* $fExceptionPatternMatchFail_$cshow */ = function(_95/* s4nv4 */){
  return E(E(_95/* s4nv4 */).a);
},
_96/* $fExceptionPatternMatchFail_$ctoException */ = function(_97/* B1 */){
  return new T2(0,_98/* Control.Exception.Base.$fExceptionPatternMatchFail */,_97/* B1 */);
},
_99/* $fShowPatternMatchFail1 */ = function(_9a/* s4nqK */, _9b/* s4nqL */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_9a/* s4nqK */).a, _9b/* s4nqL */);});
},
_9c/* $fShowPatternMatchFail_$cshowList */ = function(_9d/* s4nv2 */, _9e/* s4nv3 */){
  return new F(function(){return _5s/* GHC.Show.showList__ */(_99/* Control.Exception.Base.$fShowPatternMatchFail1 */, _9d/* s4nv2 */, _9e/* s4nv3 */);});
},
_9f/* $fShowPatternMatchFail_$cshowsPrec */ = function(_9g/* s4nv7 */, _9h/* s4nv8 */, _9i/* s4nv9 */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_9h/* s4nv8 */).a, _9i/* s4nv9 */);});
},
_9j/* $fShowPatternMatchFail */ = new T3(0,_9f/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_94/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_9c/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_98/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_8P/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_9j/* Control.Exception.Base.$fShowPatternMatchFail */,_96/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_91/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_94/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_9k/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_9l/* toException */ = function(_9m/* s2SzC */){
  return E(E(_9m/* s2SzC */).c);
},
_9n/* lvl */ = function(_9o/* s2SzX */, _9p/* s2SzY */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_9l/* GHC.Exception.toException */,_9p/* s2SzY */, _9o/* s2SzX */));
  }));});
},
_9q/* throw1 */ = function(_9r/* B2 */, _9s/* B1 */){
  return new F(function(){return _9n/* GHC.Exception.lvl */(_9r/* B2 */, _9s/* B1 */);});
},
_9t/* $wspan */ = function(_9u/* s9vU */, _9v/* s9vV */){
  var _9w/* s9vW */ = E(_9v/* s9vV */);
  if(!_9w/* s9vW */._){
    return new T2(0,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */);
  }else{
    var _9x/* s9vX */ = _9w/* s9vW */.a;
    if(!B(A1(_9u/* s9vU */,_9x/* s9vX */))){
      return new T2(0,_k/* GHC.Types.[] */,_9w/* s9vW */);
    }else{
      var _9y/* s9w0 */ = new T(function(){
        var _9z/* s9w1 */ = B(_9t/* GHC.List.$wspan */(_9u/* s9vU */, _9w/* s9vW */.b));
        return new T2(0,_9z/* s9w1 */.a,_9z/* s9w1 */.b);
      });
      return new T2(0,new T2(1,_9x/* s9vX */,new T(function(){
        return E(E(_9y/* s9w0 */).a);
      })),new T(function(){
        return E(E(_9y/* s9w0 */).b);
      }));
    }
  }
},
_9A/* untangle1 */ = 32,
_9B/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_9C/* untangle3 */ = function(_9D/* s3K4R */){
  return (E(_9D/* s3K4R */)==124) ? false : true;
},
_9E/* untangle */ = function(_9F/* s3K5K */, _9G/* s3K5L */){
  var _9H/* s3K5N */ = B(_9t/* GHC.List.$wspan */(_9C/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_9F/* s3K5K */)))),
  _9I/* s3K5O */ = _9H/* s3K5N */.a,
  _9J/* s3K5Q */ = function(_9K/* s3K5R */, _9L/* s3K5S */){
    var _9M/* s3K5V */ = new T(function(){
      var _9N/* s3K5U */ = new T(function(){
        return B(_7/* GHC.Base.++ */(_9G/* s3K5L */, new T(function(){
          return B(_7/* GHC.Base.++ */(_9L/* s3K5S */, _9B/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _9N/* s3K5U */));
    },1);
    return new F(function(){return _7/* GHC.Base.++ */(_9K/* s3K5R */, _9M/* s3K5V */);});
  },
  _9O/* s3K5W */ = E(_9H/* s3K5N */.b);
  if(!_9O/* s3K5W */._){
    return new F(function(){return _9J/* s3K5Q */(_9I/* s3K5O */, _k/* GHC.Types.[] */);});
  }else{
    if(E(_9O/* s3K5W */.a)==124){
      return new F(function(){return _9J/* s3K5Q */(_9I/* s3K5O */, new T2(1,_9A/* GHC.IO.Exception.untangle1 */,_9O/* s3K5W */.b));});
    }else{
      return new F(function(){return _9J/* s3K5Q */(_9I/* s3K5O */, _k/* GHC.Types.[] */);});
    }
  }
},
_9P/* patError */ = function(_9Q/* s4nwI */){
  return new F(function(){return _9q/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_9E/* GHC.IO.Exception.untangle */(_9Q/* s4nwI */, _9k/* Control.Exception.Base.lvl3 */));
  })), _98/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_9R/* lvl2 */ = new T(function(){
  return B(_9P/* Control.Exception.Base.patError */("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));
}),
_9S/* $fAlternativeP_$c<|> */ = function(_9T/* s1iBo */, _9U/* s1iBp */){
  var _9V/* s1iBq */ = function(_9W/* s1iBr */){
    var _9X/* s1iBs */ = E(_9U/* s1iBp */);
    if(_9X/* s1iBs */._==3){
      return new T2(3,_9X/* s1iBs */.a,new T(function(){
        return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_9T/* s1iBo */, _9X/* s1iBs */.b));
      }));
    }else{
      var _9Y/* s1iBt */ = E(_9T/* s1iBo */);
      if(_9Y/* s1iBt */._==2){
        return E(_9X/* s1iBs */);
      }else{
        var _9Z/* s1iBu */ = E(_9X/* s1iBs */);
        if(_9Z/* s1iBu */._==2){
          return E(_9Y/* s1iBt */);
        }else{
          var _a0/* s1iBv */ = function(_a1/* s1iBw */){
            var _a2/* s1iBx */ = E(_9Z/* s1iBu */);
            if(_a2/* s1iBx */._==4){
              var _a3/* s1iBU */ = function(_a4/* s1iBR */){
                return new T1(4,new T(function(){
                  return B(_7/* GHC.Base.++ */(B(_8r/* Text.ParserCombinators.ReadP.run */(_9Y/* s1iBt */, _a4/* s1iBR */)), _a2/* s1iBx */.a));
                }));
              };
              return new T1(1,_a3/* s1iBU */);
            }else{
              var _a5/* s1iBy */ = E(_9Y/* s1iBt */);
              if(_a5/* s1iBy */._==1){
                var _a6/* s1iBF */ = _a5/* s1iBy */.a,
                _a7/* s1iBG */ = E(_a2/* s1iBx */);
                if(!_a7/* s1iBG */._){
                  return new T1(1,function(_a8/* s1iBI */){
                    return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_a6/* s1iBF */,_a8/* s1iBI */)), _a7/* s1iBG */);});
                  });
                }else{
                  var _a9/* s1iBP */ = function(_aa/* s1iBM */){
                    return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_a6/* s1iBF */,_aa/* s1iBM */)), new T(function(){
                      return B(A1(_a7/* s1iBG */.a,_aa/* s1iBM */));
                    }));});
                  };
                  return new T1(1,_a9/* s1iBP */);
                }
              }else{
                var _ab/* s1iBz */ = E(_a2/* s1iBx */);
                if(!_ab/* s1iBz */._){
                  return E(_9R/* Text.ParserCombinators.ReadP.lvl2 */);
                }else{
                  var _ac/* s1iBE */ = function(_ad/* s1iBC */){
                    return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_a5/* s1iBy */, new T(function(){
                      return B(A1(_ab/* s1iBz */.a,_ad/* s1iBC */));
                    }));});
                  };
                  return new T1(1,_ac/* s1iBE */);
                }
              }
            }
          },
          _ae/* s1iBV */ = E(_9Y/* s1iBt */);
          switch(_ae/* s1iBV */._){
            case 1:
              var _af/* s1iBX */ = E(_9Z/* s1iBu */);
              if(_af/* s1iBX */._==4){
                var _ag/* s1iC3 */ = function(_ah/* s1iBZ */){
                  return new T1(4,new T(function(){
                    return B(_7/* GHC.Base.++ */(B(_8r/* Text.ParserCombinators.ReadP.run */(B(A1(_ae/* s1iBV */.a,_ah/* s1iBZ */)), _ah/* s1iBZ */)), _af/* s1iBX */.a));
                  }));
                };
                return new T1(1,_ag/* s1iC3 */);
              }else{
                return new F(function(){return _a0/* s1iBv */(_/* EXTERNAL */);});
              }
              break;
            case 4:
              var _ai/* s1iC4 */ = _ae/* s1iBV */.a,
              _aj/* s1iC5 */ = E(_9Z/* s1iBu */);
              switch(_aj/* s1iC5 */._){
                case 0:
                  var _ak/* s1iCa */ = function(_al/* s1iC7 */){
                    var _am/* s1iC9 */ = new T(function(){
                      return B(_7/* GHC.Base.++ */(_ai/* s1iC4 */, new T(function(){
                        return B(_8r/* Text.ParserCombinators.ReadP.run */(_aj/* s1iC5 */, _al/* s1iC7 */));
                      },1)));
                    });
                    return new T1(4,_am/* s1iC9 */);
                  };
                  return new T1(1,_ak/* s1iCa */);
                case 1:
                  var _an/* s1iCg */ = function(_ao/* s1iCc */){
                    var _ap/* s1iCf */ = new T(function(){
                      return B(_7/* GHC.Base.++ */(_ai/* s1iC4 */, new T(function(){
                        return B(_8r/* Text.ParserCombinators.ReadP.run */(B(A1(_aj/* s1iC5 */.a,_ao/* s1iCc */)), _ao/* s1iCc */));
                      },1)));
                    });
                    return new T1(4,_ap/* s1iCf */);
                  };
                  return new T1(1,_an/* s1iCg */);
                default:
                  return new T1(4,new T(function(){
                    return B(_7/* GHC.Base.++ */(_ai/* s1iC4 */, _aj/* s1iC5 */.a));
                  }));
              }
              break;
            default:
              return new F(function(){return _a0/* s1iBv */(_/* EXTERNAL */);});
          }
        }
      }
    }
  },
  _aq/* s1iCm */ = E(_9T/* s1iBo */);
  switch(_aq/* s1iCm */._){
    case 0:
      var _ar/* s1iCo */ = E(_9U/* s1iBp */);
      if(!_ar/* s1iCo */._){
        var _as/* s1iCt */ = function(_at/* s1iCq */){
          return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_aq/* s1iCm */.a,_at/* s1iCq */)), new T(function(){
            return B(A1(_ar/* s1iCo */.a,_at/* s1iCq */));
          }));});
        };
        return new T1(0,_as/* s1iCt */);
      }else{
        return new F(function(){return _9V/* s1iBq */(_/* EXTERNAL */);});
      }
      break;
    case 3:
      return new T2(3,_aq/* s1iCm */.a,new T(function(){
        return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_aq/* s1iCm */.b, _9U/* s1iBp */));
      }));
    default:
      return new F(function(){return _9V/* s1iBq */(_/* EXTERNAL */);});
  }
},
_au/* $fRead(,)3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_av/* $fRead(,)4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_aw/* $fEqChar_$c/= */ = function(_ax/* scFn */, _ay/* scFo */){
  return E(_ax/* scFn */)!=E(_ay/* scFo */);
},
_az/* $fEqChar_$c== */ = function(_aA/* scFu */, _aB/* scFv */){
  return E(_aA/* scFu */)==E(_aB/* scFv */);
},
_aC/* $fEqChar */ = new T2(0,_az/* GHC.Classes.$fEqChar_$c== */,_aw/* GHC.Classes.$fEqChar_$c/= */),
_aD/* $fEq[]_$s$c==1 */ = function(_aE/* scIY */, _aF/* scIZ */){
  while(1){
    var _aG/* scJ0 */ = E(_aE/* scIY */);
    if(!_aG/* scJ0 */._){
      return (E(_aF/* scIZ */)._==0) ? true : false;
    }else{
      var _aH/* scJ6 */ = E(_aF/* scIZ */);
      if(!_aH/* scJ6 */._){
        return false;
      }else{
        if(E(_aG/* scJ0 */.a)!=E(_aH/* scJ6 */.a)){
          return false;
        }else{
          _aE/* scIY */ = _aG/* scJ0 */.b;
          _aF/* scIZ */ = _aH/* scJ6 */.b;
          continue;
        }
      }
    }
  }
},
_aI/* $fEq[]_$s$c/=1 */ = function(_aJ/* scJE */, _aK/* scJF */){
  return (!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_aJ/* scJE */, _aK/* scJF */))) ? true : false;
},
_aL/* $fEq[]_$s$fEq[]1 */ = new T2(0,_aD/* GHC.Classes.$fEq[]_$s$c==1 */,_aI/* GHC.Classes.$fEq[]_$s$c/=1 */),
_aM/* $fAlternativeP_$c>>= */ = function(_aN/* s1iCx */, _aO/* s1iCy */){
  var _aP/* s1iCz */ = E(_aN/* s1iCx */);
  switch(_aP/* s1iCz */._){
    case 0:
      return new T1(0,function(_aQ/* s1iCB */){
        return new F(function(){return _aM/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_aP/* s1iCz */.a,_aQ/* s1iCB */)), _aO/* s1iCy */);});
      });
    case 1:
      return new T1(1,function(_aR/* s1iCF */){
        return new F(function(){return _aM/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_aP/* s1iCz */.a,_aR/* s1iCF */)), _aO/* s1iCy */);});
      });
    case 2:
      return new T0(2);
    case 3:
      return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_aO/* s1iCy */,_aP/* s1iCz */.a)), new T(function(){
        return B(_aM/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_aP/* s1iCz */.b, _aO/* s1iCy */));
      }));});
      break;
    default:
      var _aS/* s1iCN */ = function(_aT/* s1iCO */){
        var _aU/* s1iCP */ = E(_aT/* s1iCO */);
        if(!_aU/* s1iCP */._){
          return __Z/* EXTERNAL */;
        }else{
          var _aV/* s1iCS */ = E(_aU/* s1iCP */.a);
          return new F(function(){return _7/* GHC.Base.++ */(B(_8r/* Text.ParserCombinators.ReadP.run */(B(A1(_aO/* s1iCy */,_aV/* s1iCS */.a)), _aV/* s1iCS */.b)), new T(function(){
            return B(_aS/* s1iCN */(_aU/* s1iCP */.b));
          },1));});
        }
      },
      _aW/* s1iCY */ = B(_aS/* s1iCN */(_aP/* s1iCz */.a));
      return (_aW/* s1iCY */._==0) ? new T0(2) : new T1(4,_aW/* s1iCY */);
  }
},
_aX/* Fail */ = new T0(2),
_aY/* $fApplicativeP_$creturn */ = function(_aZ/* s1iBl */){
  return new T2(3,_aZ/* s1iBl */,_aX/* Text.ParserCombinators.ReadP.Fail */);
},
_b0/* <++2 */ = function(_b1/* s1iyp */, _b2/* s1iyq */){
  var _b3/* s1iyr */ = E(_b1/* s1iyp */);
  if(!_b3/* s1iyr */){
    return new F(function(){return A1(_b2/* s1iyq */,_0/* GHC.Tuple.() */);});
  }else{
    var _b4/* s1iys */ = new T(function(){
      return B(_b0/* Text.ParserCombinators.ReadP.<++2 */(_b3/* s1iyr */-1|0, _b2/* s1iyq */));
    });
    return new T1(0,function(_b5/* s1iyu */){
      return E(_b4/* s1iys */);
    });
  }
},
_b6/* $wa */ = function(_b7/* s1iD8 */, _b8/* s1iD9 */, _b9/* s1iDa */){
  var _ba/* s1iDb */ = new T(function(){
    return B(A1(_b7/* s1iD8 */,_aY/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
  }),
  _bb/* s1iDc */ = function(_bc/*  s1iDd */, _bd/*  s1iDe */, _be/*  s1iDf */, _bf/*  s1iDg */){
    while(1){
      var _bg/*  s1iDc */ = B((function(_bh/* s1iDd */, _bi/* s1iDe */, _bj/* s1iDf */, _bk/* s1iDg */){
        var _bl/* s1iDh */ = E(_bh/* s1iDd */);
        switch(_bl/* s1iDh */._){
          case 0:
            var _bm/* s1iDj */ = E(_bi/* s1iDe */);
            if(!_bm/* s1iDj */._){
              return new F(function(){return A1(_b8/* s1iD9 */,_bk/* s1iDg */);});
            }else{
              var _bn/*   s1iDf */ = _bj/* s1iDf */+1|0,
              _bo/*   s1iDg */ = _bk/* s1iDg */;
              _bc/*  s1iDd */ = B(A1(_bl/* s1iDh */.a,_bm/* s1iDj */.a));
              _bd/*  s1iDe */ = _bm/* s1iDj */.b;
              _be/*  s1iDf */ = _bn/*   s1iDf */;
              _bf/*  s1iDg */ = _bo/*   s1iDg */;
              return __continue/* EXTERNAL */;
            }
            break;
          case 1:
            var _bp/*   s1iDd */ = B(A1(_bl/* s1iDh */.a,_bi/* s1iDe */)),
            _bq/*   s1iDe */ = _bi/* s1iDe */,
            _bn/*   s1iDf */ = _bj/* s1iDf */,
            _bo/*   s1iDg */ = _bk/* s1iDg */;
            _bc/*  s1iDd */ = _bp/*   s1iDd */;
            _bd/*  s1iDe */ = _bq/*   s1iDe */;
            _be/*  s1iDf */ = _bn/*   s1iDf */;
            _bf/*  s1iDg */ = _bo/*   s1iDg */;
            return __continue/* EXTERNAL */;
          case 2:
            return new F(function(){return A1(_b8/* s1iD9 */,_bk/* s1iDg */);});
            break;
          case 3:
            var _br/* s1iDs */ = new T(function(){
              return B(_aM/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_bl/* s1iDh */, _bk/* s1iDg */));
            });
            return new F(function(){return _b0/* Text.ParserCombinators.ReadP.<++2 */(_bj/* s1iDf */, function(_bs/* s1iDt */){
              return E(_br/* s1iDs */);
            });});
            break;
          default:
            return new F(function(){return _aM/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_bl/* s1iDh */, _bk/* s1iDg */);});
        }
      })(_bc/*  s1iDd */, _bd/*  s1iDe */, _be/*  s1iDf */, _bf/*  s1iDg */));
      if(_bg/*  s1iDc */!=__continue/* EXTERNAL */){
        return _bg/*  s1iDc */;
      }
    }
  };
  return function(_bt/* s1iDw */){
    return new F(function(){return _bb/* s1iDc */(_ba/* s1iDb */, _bt/* s1iDw */, 0, _b9/* s1iDa */);});
  };
},
_bu/* munch3 */ = function(_bv/* s1iyo */){
  return new F(function(){return A1(_bv/* s1iyo */,_k/* GHC.Types.[] */);});
},
_bw/* $wa3 */ = function(_bx/* s1iyQ */, _by/* s1iyR */){
  var _bz/* s1iyS */ = function(_bA/* s1iyT */){
    var _bB/* s1iyU */ = E(_bA/* s1iyT */);
    if(!_bB/* s1iyU */._){
      return E(_bu/* Text.ParserCombinators.ReadP.munch3 */);
    }else{
      var _bC/* s1iyV */ = _bB/* s1iyU */.a;
      if(!B(A1(_bx/* s1iyQ */,_bC/* s1iyV */))){
        return E(_bu/* Text.ParserCombinators.ReadP.munch3 */);
      }else{
        var _bD/* s1iyY */ = new T(function(){
          return B(_bz/* s1iyS */(_bB/* s1iyU */.b));
        }),
        _bE/* s1iz6 */ = function(_bF/* s1iyZ */){
          var _bG/* s1iz0 */ = new T(function(){
            return B(A1(_bD/* s1iyY */,function(_bH/* s1iz1 */){
              return new F(function(){return A1(_bF/* s1iyZ */,new T2(1,_bC/* s1iyV */,_bH/* s1iz1 */));});
            }));
          });
          return new T1(0,function(_bI/* s1iz4 */){
            return E(_bG/* s1iz0 */);
          });
        };
        return E(_bE/* s1iz6 */);
      }
    }
  };
  return function(_bJ/* s1iz7 */){
    return new F(function(){return A2(_bz/* s1iyS */,_bJ/* s1iz7 */, _by/* s1iyR */);});
  };
},
_bK/* EOF */ = new T0(6),
_bL/* id */ = function(_bM/* s3aI */){
  return E(_bM/* s3aI */);
},
_bN/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("valDig: Bad base"));
}),
_bO/* readDecP2 */ = new T(function(){
  return B(err/* EXTERNAL */(_bN/* Text.Read.Lex.lvl37 */));
}),
_bP/* $wa6 */ = function(_bQ/* s1oaO */, _bR/* s1oaP */){
  var _bS/* s1oaQ */ = function(_bT/* s1oaR */, _bU/* s1oaS */){
    var _bV/* s1oaT */ = E(_bT/* s1oaR */);
    if(!_bV/* s1oaT */._){
      var _bW/* s1oaU */ = new T(function(){
        return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
      });
      return function(_bX/* s1oaV */){
        return new F(function(){return A1(_bX/* s1oaV */,_bW/* s1oaU */);});
      };
    }else{
      var _bY/* s1ob1 */ = E(_bV/* s1oaT */.a),
      _bZ/* s1ob3 */ = function(_c0/* s1ob4 */){
        var _c1/* s1ob5 */ = new T(function(){
          return B(_bS/* s1oaQ */(_bV/* s1oaT */.b, function(_c2/* s1ob6 */){
            return new F(function(){return A1(_bU/* s1oaS */,new T2(1,_c0/* s1ob4 */,_c2/* s1ob6 */));});
          }));
        }),
        _c3/* s1obd */ = function(_c4/* s1ob9 */){
          var _c5/* s1oba */ = new T(function(){
            return B(A1(_c1/* s1ob5 */,_c4/* s1ob9 */));
          });
          return new T1(0,function(_c6/* s1obb */){
            return E(_c5/* s1oba */);
          });
        };
        return E(_c3/* s1obd */);
      };
      switch(E(_bQ/* s1oaO */)){
        case 8:
          if(48>_bY/* s1ob1 */){
            var _c7/* s1obi */ = new T(function(){
              return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
            });
            return function(_c8/* s1obj */){
              return new F(function(){return A1(_c8/* s1obj */,_c7/* s1obi */);});
            };
          }else{
            if(_bY/* s1ob1 */>55){
              var _c9/* s1obn */ = new T(function(){
                return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
              });
              return function(_ca/* s1obo */){
                return new F(function(){return A1(_ca/* s1obo */,_c9/* s1obn */);});
              };
            }else{
              return new F(function(){return _bZ/* s1ob3 */(_bY/* s1ob1 */-48|0);});
            }
          }
          break;
        case 10:
          if(48>_bY/* s1ob1 */){
            var _cb/* s1obv */ = new T(function(){
              return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
            });
            return function(_cc/* s1obw */){
              return new F(function(){return A1(_cc/* s1obw */,_cb/* s1obv */);});
            };
          }else{
            if(_bY/* s1ob1 */>57){
              var _cd/* s1obA */ = new T(function(){
                return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
              });
              return function(_ce/* s1obB */){
                return new F(function(){return A1(_ce/* s1obB */,_cd/* s1obA */);});
              };
            }else{
              return new F(function(){return _bZ/* s1ob3 */(_bY/* s1ob1 */-48|0);});
            }
          }
          break;
        case 16:
          if(48>_bY/* s1ob1 */){
            if(97>_bY/* s1ob1 */){
              if(65>_bY/* s1ob1 */){
                var _cf/* s1obM */ = new T(function(){
                  return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                });
                return function(_cg/* s1obN */){
                  return new F(function(){return A1(_cg/* s1obN */,_cf/* s1obM */);});
                };
              }else{
                if(_bY/* s1ob1 */>70){
                  var _ch/* s1obR */ = new T(function(){
                    return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                  });
                  return function(_ci/* s1obS */){
                    return new F(function(){return A1(_ci/* s1obS */,_ch/* s1obR */);});
                  };
                }else{
                  return new F(function(){return _bZ/* s1ob3 */((_bY/* s1ob1 */-65|0)+10|0);});
                }
              }
            }else{
              if(_bY/* s1ob1 */>102){
                if(65>_bY/* s1ob1 */){
                  var _cj/* s1oc2 */ = new T(function(){
                    return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                  });
                  return function(_ck/* s1oc3 */){
                    return new F(function(){return A1(_ck/* s1oc3 */,_cj/* s1oc2 */);});
                  };
                }else{
                  if(_bY/* s1ob1 */>70){
                    var _cl/* s1oc7 */ = new T(function(){
                      return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                    });
                    return function(_cm/* s1oc8 */){
                      return new F(function(){return A1(_cm/* s1oc8 */,_cl/* s1oc7 */);});
                    };
                  }else{
                    return new F(function(){return _bZ/* s1ob3 */((_bY/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                return new F(function(){return _bZ/* s1ob3 */((_bY/* s1ob1 */-97|0)+10|0);});
              }
            }
          }else{
            if(_bY/* s1ob1 */>57){
              if(97>_bY/* s1ob1 */){
                if(65>_bY/* s1ob1 */){
                  var _cn/* s1oco */ = new T(function(){
                    return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                  });
                  return function(_co/* s1ocp */){
                    return new F(function(){return A1(_co/* s1ocp */,_cn/* s1oco */);});
                  };
                }else{
                  if(_bY/* s1ob1 */>70){
                    var _cp/* s1oct */ = new T(function(){
                      return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                    });
                    return function(_cq/* s1ocu */){
                      return new F(function(){return A1(_cq/* s1ocu */,_cp/* s1oct */);});
                    };
                  }else{
                    return new F(function(){return _bZ/* s1ob3 */((_bY/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                if(_bY/* s1ob1 */>102){
                  if(65>_bY/* s1ob1 */){
                    var _cr/* s1ocE */ = new T(function(){
                      return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                    });
                    return function(_cs/* s1ocF */){
                      return new F(function(){return A1(_cs/* s1ocF */,_cr/* s1ocE */);});
                    };
                  }else{
                    if(_bY/* s1ob1 */>70){
                      var _ct/* s1ocJ */ = new T(function(){
                        return B(A1(_bU/* s1oaS */,_k/* GHC.Types.[] */));
                      });
                      return function(_cu/* s1ocK */){
                        return new F(function(){return A1(_cu/* s1ocK */,_ct/* s1ocJ */);});
                      };
                    }else{
                      return new F(function(){return _bZ/* s1ob3 */((_bY/* s1ob1 */-65|0)+10|0);});
                    }
                  }
                }else{
                  return new F(function(){return _bZ/* s1ob3 */((_bY/* s1ob1 */-97|0)+10|0);});
                }
              }
            }else{
              return new F(function(){return _bZ/* s1ob3 */(_bY/* s1ob1 */-48|0);});
            }
          }
          break;
        default:
          return E(_bO/* Text.Read.Lex.readDecP2 */);
      }
    }
  },
  _cv/* s1ocX */ = function(_cw/* s1ocY */){
    var _cx/* s1ocZ */ = E(_cw/* s1ocY */);
    if(!_cx/* s1ocZ */._){
      return new T0(2);
    }else{
      return new F(function(){return A1(_bR/* s1oaP */,_cx/* s1ocZ */);});
    }
  };
  return function(_cy/* s1od2 */){
    return new F(function(){return A3(_bS/* s1oaQ */,_cy/* s1od2 */, _bL/* GHC.Base.id */, _cv/* s1ocX */);});
  };
},
_cz/* lvl41 */ = 16,
_cA/* lvl42 */ = 8,
_cB/* $wa7 */ = function(_cC/* s1od4 */){
  var _cD/* s1od5 */ = function(_cE/* s1od6 */){
    return new F(function(){return A1(_cC/* s1od4 */,new T1(5,new T2(0,_cA/* Text.Read.Lex.lvl42 */,_cE/* s1od6 */)));});
  },
  _cF/* s1od9 */ = function(_cG/* s1oda */){
    return new F(function(){return A1(_cC/* s1od4 */,new T1(5,new T2(0,_cz/* Text.Read.Lex.lvl41 */,_cG/* s1oda */)));});
  },
  _cH/* s1odd */ = function(_cI/* s1ode */){
    switch(E(_cI/* s1ode */)){
      case 79:
        return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cA/* Text.Read.Lex.lvl42 */, _cD/* s1od5 */)));
      case 88:
        return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cz/* Text.Read.Lex.lvl41 */, _cF/* s1od9 */)));
      case 111:
        return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cA/* Text.Read.Lex.lvl42 */, _cD/* s1od5 */)));
      case 120:
        return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cz/* Text.Read.Lex.lvl41 */, _cF/* s1od9 */)));
      default:
        return new T0(2);
    }
  };
  return function(_cJ/* s1odr */){
    return (E(_cJ/* s1odr */)==48) ? E(new T1(0,_cH/* s1odd */)) : new T0(2);
  };
},
_cK/* a2 */ = function(_cL/* s1odw */){
  return new T1(0,B(_cB/* Text.Read.Lex.$wa7 */(_cL/* s1odw */)));
},
_cM/* a */ = function(_cN/* s1o94 */){
  return new F(function(){return A1(_cN/* s1o94 */,_4y/* GHC.Base.Nothing */);});
},
_cO/* a1 */ = function(_cP/* s1o95 */){
  return new F(function(){return A1(_cP/* s1o95 */,_4y/* GHC.Base.Nothing */);});
},
_cQ/* lvl */ = 10,
_cR/* log2I1 */ = new T1(0,1),
_cS/* lvl2 */ = new T1(0,2147483647),
_cT/* plusInteger */ = function(_cU/* s1Qe */, _cV/* s1Qf */){
  while(1){
    var _cW/* s1Qg */ = E(_cU/* s1Qe */);
    if(!_cW/* s1Qg */._){
      var _cX/* s1Qh */ = _cW/* s1Qg */.a,
      _cY/* s1Qi */ = E(_cV/* s1Qf */);
      if(!_cY/* s1Qi */._){
        var _cZ/* s1Qj */ = _cY/* s1Qi */.a,
        _d0/* s1Qk */ = addC/* EXTERNAL */(_cX/* s1Qh */, _cZ/* s1Qj */);
        if(!E(_d0/* s1Qk */.b)){
          return new T1(0,_d0/* s1Qk */.a);
        }else{
          _cU/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_cX/* s1Qh */));
          _cV/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_cZ/* s1Qj */));
          continue;
        }
      }else{
        _cU/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_cX/* s1Qh */));
        _cV/* s1Qf */ = _cY/* s1Qi */;
        continue;
      }
    }else{
      var _d1/* s1Qz */ = E(_cV/* s1Qf */);
      if(!_d1/* s1Qz */._){
        _cU/* s1Qe */ = _cW/* s1Qg */;
        _cV/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_d1/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_cW/* s1Qg */.a, _d1/* s1Qz */.a));
      }
    }
  }
},
_d2/* lvl3 */ = new T(function(){
  return B(_cT/* GHC.Integer.Type.plusInteger */(_cS/* GHC.Integer.Type.lvl2 */, _cR/* GHC.Integer.Type.log2I1 */));
}),
_d3/* negateInteger */ = function(_d4/* s1QH */){
  var _d5/* s1QI */ = E(_d4/* s1QH */);
  if(!_d5/* s1QI */._){
    var _d6/* s1QK */ = E(_d5/* s1QI */.a);
    return (_d6/* s1QK */==(-2147483648)) ? E(_d2/* GHC.Integer.Type.lvl3 */) : new T1(0, -_d6/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_d5/* s1QI */.a));
  }
},
_d7/* numberToFixed1 */ = new T1(0,10),
_d8/* $wlenAcc */ = function(_d9/* s9Bd */, _da/* s9Be */){
  while(1){
    var _db/* s9Bf */ = E(_d9/* s9Bd */);
    if(!_db/* s9Bf */._){
      return E(_da/* s9Be */);
    }else{
      var _dc/*  s9Be */ = _da/* s9Be */+1|0;
      _d9/* s9Bd */ = _db/* s9Bf */.b;
      _da/* s9Be */ = _dc/*  s9Be */;
      continue;
    }
  }
},
_dd/* smallInteger */ = function(_de/* B1 */){
  return new T1(0,_de/* B1 */);
},
_df/* numberToFixed2 */ = function(_dg/* s1o9e */){
  return new F(function(){return _dd/* GHC.Integer.Type.smallInteger */(E(_dg/* s1o9e */));});
},
_dh/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("this should not happen"));
}),
_di/* lvl40 */ = new T(function(){
  return B(err/* EXTERNAL */(_dh/* Text.Read.Lex.lvl39 */));
}),
_dj/* timesInteger */ = function(_dk/* s1PN */, _dl/* s1PO */){
  while(1){
    var _dm/* s1PP */ = E(_dk/* s1PN */);
    if(!_dm/* s1PP */._){
      var _dn/* s1PQ */ = _dm/* s1PP */.a,
      _do/* s1PR */ = E(_dl/* s1PO */);
      if(!_do/* s1PR */._){
        var _dp/* s1PS */ = _do/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_dn/* s1PQ */, _dp/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_dn/* s1PQ */, _dp/* s1PS */)|0);
        }else{
          _dk/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_dn/* s1PQ */));
          _dl/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_dp/* s1PS */));
          continue;
        }
      }else{
        _dk/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_dn/* s1PQ */));
        _dl/* s1PO */ = _do/* s1PR */;
        continue;
      }
    }else{
      var _dq/* s1Q6 */ = E(_dl/* s1PO */);
      if(!_dq/* s1Q6 */._){
        _dk/* s1PN */ = _dm/* s1PP */;
        _dl/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_dq/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_dm/* s1PP */.a, _dq/* s1Q6 */.a));
      }
    }
  }
},
_dr/* combine */ = function(_ds/* s1o9h */, _dt/* s1o9i */){
  var _du/* s1o9j */ = E(_dt/* s1o9i */);
  if(!_du/* s1o9j */._){
    return __Z/* EXTERNAL */;
  }else{
    var _dv/* s1o9m */ = E(_du/* s1o9j */.b);
    return (_dv/* s1o9m */._==0) ? E(_di/* Text.Read.Lex.lvl40 */) : new T2(1,B(_cT/* GHC.Integer.Type.plusInteger */(B(_dj/* GHC.Integer.Type.timesInteger */(_du/* s1o9j */.a, _ds/* s1o9h */)), _dv/* s1o9m */.a)),new T(function(){
      return B(_dr/* Text.Read.Lex.combine */(_ds/* s1o9h */, _dv/* s1o9m */.b));
    }));
  }
},
_dw/* numberToFixed3 */ = new T1(0,0),
_dx/* numberToFixed_go */ = function(_dy/*  s1o9s */, _dz/*  s1o9t */, _dA/*  s1o9u */){
  while(1){
    var _dB/*  numberToFixed_go */ = B((function(_dC/* s1o9s */, _dD/* s1o9t */, _dE/* s1o9u */){
      var _dF/* s1o9v */ = E(_dE/* s1o9u */);
      if(!_dF/* s1o9v */._){
        return E(_dw/* Text.Read.Lex.numberToFixed3 */);
      }else{
        if(!E(_dF/* s1o9v */.b)._){
          return E(_dF/* s1o9v */.a);
        }else{
          var _dG/* s1o9B */ = E(_dD/* s1o9t */);
          if(_dG/* s1o9B */<=40){
            var _dH/* s1o9F */ = function(_dI/* s1o9G */, _dJ/* s1o9H */){
              while(1){
                var _dK/* s1o9I */ = E(_dJ/* s1o9H */);
                if(!_dK/* s1o9I */._){
                  return E(_dI/* s1o9G */);
                }else{
                  var _dL/*  s1o9G */ = B(_cT/* GHC.Integer.Type.plusInteger */(B(_dj/* GHC.Integer.Type.timesInteger */(_dI/* s1o9G */, _dC/* s1o9s */)), _dK/* s1o9I */.a));
                  _dI/* s1o9G */ = _dL/*  s1o9G */;
                  _dJ/* s1o9H */ = _dK/* s1o9I */.b;
                  continue;
                }
              }
            };
            return new F(function(){return _dH/* s1o9F */(_dw/* Text.Read.Lex.numberToFixed3 */, _dF/* s1o9v */);});
          }else{
            var _dM/* s1o9N */ = B(_dj/* GHC.Integer.Type.timesInteger */(_dC/* s1o9s */, _dC/* s1o9s */));
            if(!(_dG/* s1o9B */%2)){
              var _dN/*   s1o9u */ = B(_dr/* Text.Read.Lex.combine */(_dC/* s1o9s */, _dF/* s1o9v */));
              _dy/*  s1o9s */ = _dM/* s1o9N */;
              _dz/*  s1o9t */ = quot/* EXTERNAL */(_dG/* s1o9B */+1|0, 2);
              _dA/*  s1o9u */ = _dN/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }else{
              var _dN/*   s1o9u */ = B(_dr/* Text.Read.Lex.combine */(_dC/* s1o9s */, new T2(1,_dw/* Text.Read.Lex.numberToFixed3 */,_dF/* s1o9v */)));
              _dy/*  s1o9s */ = _dM/* s1o9N */;
              _dz/*  s1o9t */ = quot/* EXTERNAL */(_dG/* s1o9B */+1|0, 2);
              _dA/*  s1o9u */ = _dN/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }
          }
        }
      }
    })(_dy/*  s1o9s */, _dz/*  s1o9t */, _dA/*  s1o9u */));
    if(_dB/*  numberToFixed_go */!=__continue/* EXTERNAL */){
      return _dB/*  numberToFixed_go */;
    }
  }
},
_dO/* valInteger */ = function(_dP/* s1off */, _dQ/* s1ofg */){
  return new F(function(){return _dx/* Text.Read.Lex.numberToFixed_go */(_dP/* s1off */, new T(function(){
    return B(_d8/* GHC.List.$wlenAcc */(_dQ/* s1ofg */, 0));
  },1), B(_8G/* GHC.Base.map */(_df/* Text.Read.Lex.numberToFixed2 */, _dQ/* s1ofg */)));});
},
_dR/* a26 */ = function(_dS/* s1og4 */){
  var _dT/* s1og5 */ = new T(function(){
    var _dU/* s1ogC */ = new T(function(){
      var _dV/* s1ogz */ = function(_dW/* s1ogw */){
        return new F(function(){return A1(_dS/* s1og4 */,new T1(1,new T(function(){
          return B(_dO/* Text.Read.Lex.valInteger */(_d7/* Text.Read.Lex.numberToFixed1 */, _dW/* s1ogw */));
        })));});
      };
      return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cQ/* Text.Read.Lex.lvl */, _dV/* s1ogz */)));
    }),
    _dX/* s1ogt */ = function(_dY/* s1ogj */){
      if(E(_dY/* s1ogj */)==43){
        var _dZ/* s1ogq */ = function(_e0/* s1ogn */){
          return new F(function(){return A1(_dS/* s1og4 */,new T1(1,new T(function(){
            return B(_dO/* Text.Read.Lex.valInteger */(_d7/* Text.Read.Lex.numberToFixed1 */, _e0/* s1ogn */));
          })));});
        };
        return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cQ/* Text.Read.Lex.lvl */, _dZ/* s1ogq */)));
      }else{
        return new T0(2);
      }
    },
    _e1/* s1ogh */ = function(_e2/* s1og6 */){
      if(E(_e2/* s1og6 */)==45){
        var _e3/* s1oge */ = function(_e4/* s1oga */){
          return new F(function(){return A1(_dS/* s1og4 */,new T1(1,new T(function(){
            return B(_d3/* GHC.Integer.Type.negateInteger */(B(_dO/* Text.Read.Lex.valInteger */(_d7/* Text.Read.Lex.numberToFixed1 */, _e4/* s1oga */))));
          })));});
        };
        return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cQ/* Text.Read.Lex.lvl */, _e3/* s1oge */)));
      }else{
        return new T0(2);
      }
    };
    return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_e1/* s1ogh */), new T1(0,_dX/* s1ogt */))), _dU/* s1ogC */));
  });
  return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_e5/* s1ogD */){
    return (E(_e5/* s1ogD */)==101) ? E(_dT/* s1og5 */) : new T0(2);
  }), new T1(0,function(_e6/* s1ogJ */){
    return (E(_e6/* s1ogJ */)==69) ? E(_dT/* s1og5 */) : new T0(2);
  }));});
},
_e7/* $wa8 */ = function(_e8/* s1odz */){
  var _e9/* s1odA */ = function(_ea/* s1odB */){
    return new F(function(){return A1(_e8/* s1odz */,new T1(1,_ea/* s1odB */));});
  };
  return function(_eb/* s1odD */){
    return (E(_eb/* s1odD */)==46) ? new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_cQ/* Text.Read.Lex.lvl */, _e9/* s1odA */))) : new T0(2);
  };
},
_ec/* a3 */ = function(_ed/* s1odK */){
  return new T1(0,B(_e7/* Text.Read.Lex.$wa8 */(_ed/* s1odK */)));
},
_ee/* $wa10 */ = function(_ef/* s1ogP */){
  var _eg/* s1oh1 */ = function(_eh/* s1ogQ */){
    var _ei/* s1ogY */ = function(_ej/* s1ogR */){
      return new T1(1,B(_b6/* Text.ParserCombinators.ReadP.$wa */(_dR/* Text.Read.Lex.a26 */, _cM/* Text.Read.Lex.a */, function(_ek/* s1ogS */){
        return new F(function(){return A1(_ef/* s1ogP */,new T1(5,new T3(1,_eh/* s1ogQ */,_ej/* s1ogR */,_ek/* s1ogS */)));});
      })));
    };
    return new T1(1,B(_b6/* Text.ParserCombinators.ReadP.$wa */(_ec/* Text.Read.Lex.a3 */, _cO/* Text.Read.Lex.a1 */, _ei/* s1ogY */)));
  };
  return new F(function(){return _bP/* Text.Read.Lex.$wa6 */(_cQ/* Text.Read.Lex.lvl */, _eg/* s1oh1 */);});
},
_el/* a27 */ = function(_em/* s1oh2 */){
  return new T1(1,B(_ee/* Text.Read.Lex.$wa10 */(_em/* s1oh2 */)));
},
_en/* == */ = function(_eo/* scBJ */){
  return E(E(_eo/* scBJ */).a);
},
_ep/* elem */ = function(_eq/* s9uW */, _er/* s9uX */, _es/* s9uY */){
  while(1){
    var _et/* s9uZ */ = E(_es/* s9uY */);
    if(!_et/* s9uZ */._){
      return false;
    }else{
      if(!B(A3(_en/* GHC.Classes.== */,_eq/* s9uW */, _er/* s9uX */, _et/* s9uZ */.a))){
        _es/* s9uY */ = _et/* s9uZ */.b;
        continue;
      }else{
        return true;
      }
    }
  }
},
_eu/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!@#$%&*+./<=>?\\^|:-~"));
}),
_ev/* a6 */ = function(_ew/* s1odZ */){
  return new F(function(){return _ep/* GHC.List.elem */(_aC/* GHC.Classes.$fEqChar */, _ew/* s1odZ */, _eu/* Text.Read.Lex.lvl44 */);});
},
_ex/* $wa9 */ = function(_ey/* s1odN */){
  var _ez/* s1odO */ = new T(function(){
    return B(A1(_ey/* s1odN */,_cA/* Text.Read.Lex.lvl42 */));
  }),
  _eA/* s1odP */ = new T(function(){
    return B(A1(_ey/* s1odN */,_cz/* Text.Read.Lex.lvl41 */));
  });
  return function(_eB/* s1odQ */){
    switch(E(_eB/* s1odQ */)){
      case 79:
        return E(_ez/* s1odO */);
      case 88:
        return E(_eA/* s1odP */);
      case 111:
        return E(_ez/* s1odO */);
      case 120:
        return E(_eA/* s1odP */);
      default:
        return new T0(2);
    }
  };
},
_eC/* a4 */ = function(_eD/* s1odV */){
  return new T1(0,B(_ex/* Text.Read.Lex.$wa9 */(_eD/* s1odV */)));
},
_eE/* a5 */ = function(_eF/* s1odY */){
  return new F(function(){return A1(_eF/* s1odY */,_cQ/* Text.Read.Lex.lvl */);});
},
_eG/* chr2 */ = function(_eH/* sjTv */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Prelude.chr: bad argument: ", new T(function(){
    return B(_1M/* GHC.Show.$wshowSignedInt */(9, _eH/* sjTv */, _k/* GHC.Types.[] */));
  }))));});
},
_eI/* integerToInt */ = function(_eJ/* s1Rv */){
  var _eK/* s1Rw */ = E(_eJ/* s1Rv */);
  if(!_eK/* s1Rw */._){
    return E(_eK/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_eK/* s1Rw */.a);});
  }
},
_eL/* leInteger */ = function(_eM/* s1Gp */, _eN/* s1Gq */){
  var _eO/* s1Gr */ = E(_eM/* s1Gp */);
  if(!_eO/* s1Gr */._){
    var _eP/* s1Gs */ = _eO/* s1Gr */.a,
    _eQ/* s1Gt */ = E(_eN/* s1Gq */);
    return (_eQ/* s1Gt */._==0) ? _eP/* s1Gs */<=_eQ/* s1Gt */.a : I_compareInt/* EXTERNAL */(_eQ/* s1Gt */.a, _eP/* s1Gs */)>=0;
  }else{
    var _eR/* s1GA */ = _eO/* s1Gr */.a,
    _eS/* s1GB */ = E(_eN/* s1Gq */);
    return (_eS/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_eR/* s1GA */, _eS/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_eR/* s1GA */, _eS/* s1GB */.a)<=0;
  }
},
_eT/* pfail1 */ = function(_eU/* s1izT */){
  return new T0(2);
},
_eV/* choice */ = function(_eW/* s1iDZ */){
  var _eX/* s1iE0 */ = E(_eW/* s1iDZ */);
  if(!_eX/* s1iE0 */._){
    return E(_eT/* Text.ParserCombinators.ReadP.pfail1 */);
  }else{
    var _eY/* s1iE1 */ = _eX/* s1iE0 */.a,
    _eZ/* s1iE3 */ = E(_eX/* s1iE0 */.b);
    if(!_eZ/* s1iE3 */._){
      return E(_eY/* s1iE1 */);
    }else{
      var _f0/* s1iE6 */ = new T(function(){
        return B(_eV/* Text.ParserCombinators.ReadP.choice */(_eZ/* s1iE3 */));
      }),
      _f1/* s1iEa */ = function(_f2/* s1iE7 */){
        return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_eY/* s1iE1 */,_f2/* s1iE7 */)), new T(function(){
          return B(A1(_f0/* s1iE6 */,_f2/* s1iE7 */));
        }));});
      };
      return E(_f1/* s1iEa */);
    }
  }
},
_f3/* $wa6 */ = function(_f4/* s1izU */, _f5/* s1izV */){
  var _f6/* s1izW */ = function(_f7/* s1izX */, _f8/* s1izY */, _f9/* s1izZ */){
    var _fa/* s1iA0 */ = E(_f7/* s1izX */);
    if(!_fa/* s1iA0 */._){
      return new F(function(){return A1(_f9/* s1izZ */,_f4/* s1izU */);});
    }else{
      var _fb/* s1iA3 */ = E(_f8/* s1izY */);
      if(!_fb/* s1iA3 */._){
        return new T0(2);
      }else{
        if(E(_fa/* s1iA0 */.a)!=E(_fb/* s1iA3 */.a)){
          return new T0(2);
        }else{
          var _fc/* s1iAc */ = new T(function(){
            return B(_f6/* s1izW */(_fa/* s1iA0 */.b, _fb/* s1iA3 */.b, _f9/* s1izZ */));
          });
          return new T1(0,function(_fd/* s1iAd */){
            return E(_fc/* s1iAc */);
          });
        }
      }
    }
  };
  return function(_fe/* s1iAf */){
    return new F(function(){return _f6/* s1izW */(_f4/* s1izU */, _fe/* s1iAf */, _f5/* s1izV */);});
  };
},
_ff/* a28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_fg/* lvl29 */ = 14,
_fh/* a29 */ = function(_fi/* s1onM */){
  var _fj/* s1onN */ = new T(function(){
    return B(A1(_fi/* s1onM */,_fg/* Text.Read.Lex.lvl29 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_ff/* Text.Read.Lex.a28 */, function(_fk/* s1onO */){
    return E(_fj/* s1onN */);
  })));
},
_fl/* a30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_fm/* lvl35 */ = 1,
_fn/* a31 */ = function(_fo/* s1onS */){
  var _fp/* s1onT */ = new T(function(){
    return B(A1(_fo/* s1onS */,_fm/* Text.Read.Lex.lvl35 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_fl/* Text.Read.Lex.a30 */, function(_fq/* s1onU */){
    return E(_fp/* s1onT */);
  })));
},
_fr/* a32 */ = function(_fs/* s1onY */){
  return new T1(1,B(_b6/* Text.ParserCombinators.ReadP.$wa */(_fn/* Text.Read.Lex.a31 */, _fh/* Text.Read.Lex.a29 */, _fs/* s1onY */)));
},
_ft/* a33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_fu/* lvl36 */ = 0,
_fv/* a34 */ = function(_fw/* s1oo1 */){
  var _fx/* s1oo2 */ = new T(function(){
    return B(A1(_fw/* s1oo1 */,_fu/* Text.Read.Lex.lvl36 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_ft/* Text.Read.Lex.a33 */, function(_fy/* s1oo3 */){
    return E(_fx/* s1oo2 */);
  })));
},
_fz/* a35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_fA/* lvl34 */ = 2,
_fB/* a36 */ = function(_fC/* s1oo7 */){
  var _fD/* s1oo8 */ = new T(function(){
    return B(A1(_fC/* s1oo7 */,_fA/* Text.Read.Lex.lvl34 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_fz/* Text.Read.Lex.a35 */, function(_fE/* s1oo9 */){
    return E(_fD/* s1oo8 */);
  })));
},
_fF/* a37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_fG/* lvl33 */ = 3,
_fH/* a38 */ = function(_fI/* s1ood */){
  var _fJ/* s1ooe */ = new T(function(){
    return B(A1(_fI/* s1ood */,_fG/* Text.Read.Lex.lvl33 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_fF/* Text.Read.Lex.a37 */, function(_fK/* s1oof */){
    return E(_fJ/* s1ooe */);
  })));
},
_fL/* a39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_fM/* lvl32 */ = 4,
_fN/* a40 */ = function(_fO/* s1ooj */){
  var _fP/* s1ook */ = new T(function(){
    return B(A1(_fO/* s1ooj */,_fM/* Text.Read.Lex.lvl32 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_fL/* Text.Read.Lex.a39 */, function(_fQ/* s1ool */){
    return E(_fP/* s1ook */);
  })));
},
_fR/* a41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_fS/* lvl31 */ = 5,
_fT/* a42 */ = function(_fU/* s1oop */){
  var _fV/* s1ooq */ = new T(function(){
    return B(A1(_fU/* s1oop */,_fS/* Text.Read.Lex.lvl31 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_fR/* Text.Read.Lex.a41 */, function(_fW/* s1oor */){
    return E(_fV/* s1ooq */);
  })));
},
_fX/* a43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_fY/* lvl30 */ = 6,
_fZ/* a44 */ = function(_g0/* s1oov */){
  var _g1/* s1oow */ = new T(function(){
    return B(A1(_g0/* s1oov */,_fY/* Text.Read.Lex.lvl30 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_fX/* Text.Read.Lex.a43 */, function(_g2/* s1oox */){
    return E(_g1/* s1oow */);
  })));
},
_g3/* a45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_g4/* lvl7 */ = 7,
_g5/* a46 */ = function(_g6/* s1ooB */){
  var _g7/* s1ooC */ = new T(function(){
    return B(A1(_g6/* s1ooB */,_g4/* Text.Read.Lex.lvl7 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_g3/* Text.Read.Lex.a45 */, function(_g8/* s1ooD */){
    return E(_g7/* s1ooC */);
  })));
},
_g9/* a47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_ga/* lvl6 */ = 8,
_gb/* a48 */ = function(_gc/* s1ooH */){
  var _gd/* s1ooI */ = new T(function(){
    return B(A1(_gc/* s1ooH */,_ga/* Text.Read.Lex.lvl6 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_g9/* Text.Read.Lex.a47 */, function(_ge/* s1ooJ */){
    return E(_gd/* s1ooI */);
  })));
},
_gf/* a49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_gg/* lvl2 */ = 9,
_gh/* a50 */ = function(_gi/* s1ooN */){
  var _gj/* s1ooO */ = new T(function(){
    return B(A1(_gi/* s1ooN */,_gg/* Text.Read.Lex.lvl2 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gf/* Text.Read.Lex.a49 */, function(_gk/* s1ooP */){
    return E(_gj/* s1ooO */);
  })));
},
_gl/* a51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_gm/* lvl4 */ = 10,
_gn/* a52 */ = function(_go/* s1ooT */){
  var _gp/* s1ooU */ = new T(function(){
    return B(A1(_go/* s1ooT */,_gm/* Text.Read.Lex.lvl4 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gl/* Text.Read.Lex.a51 */, function(_gq/* s1ooV */){
    return E(_gp/* s1ooU */);
  })));
},
_gr/* a53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_gs/* lvl1 */ = 11,
_gt/* a54 */ = function(_gu/* s1ooZ */){
  var _gv/* s1op0 */ = new T(function(){
    return B(A1(_gu/* s1ooZ */,_gs/* Text.Read.Lex.lvl1 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gr/* Text.Read.Lex.a53 */, function(_gw/* s1op1 */){
    return E(_gv/* s1op0 */);
  })));
},
_gx/* a55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_gy/* lvl5 */ = 12,
_gz/* a56 */ = function(_gA/* s1op5 */){
  var _gB/* s1op6 */ = new T(function(){
    return B(A1(_gA/* s1op5 */,_gy/* Text.Read.Lex.lvl5 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gx/* Text.Read.Lex.a55 */, function(_gC/* s1op7 */){
    return E(_gB/* s1op6 */);
  })));
},
_gD/* a57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_gE/* lvl3 */ = 13,
_gF/* a58 */ = function(_gG/* s1opb */){
  var _gH/* s1opc */ = new T(function(){
    return B(A1(_gG/* s1opb */,_gE/* Text.Read.Lex.lvl3 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gD/* Text.Read.Lex.a57 */, function(_gI/* s1opd */){
    return E(_gH/* s1opc */);
  })));
},
_gJ/* a59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_gK/* lvl28 */ = 15,
_gL/* a60 */ = function(_gM/* s1oph */){
  var _gN/* s1opi */ = new T(function(){
    return B(A1(_gM/* s1oph */,_gK/* Text.Read.Lex.lvl28 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gJ/* Text.Read.Lex.a59 */, function(_gO/* s1opj */){
    return E(_gN/* s1opi */);
  })));
},
_gP/* a61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_gQ/* lvl27 */ = 16,
_gR/* a62 */ = function(_gS/* s1opn */){
  var _gT/* s1opo */ = new T(function(){
    return B(A1(_gS/* s1opn */,_gQ/* Text.Read.Lex.lvl27 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gP/* Text.Read.Lex.a61 */, function(_gU/* s1opp */){
    return E(_gT/* s1opo */);
  })));
},
_gV/* a63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_gW/* lvl26 */ = 17,
_gX/* a64 */ = function(_gY/* s1opt */){
  var _gZ/* s1opu */ = new T(function(){
    return B(A1(_gY/* s1opt */,_gW/* Text.Read.Lex.lvl26 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_gV/* Text.Read.Lex.a63 */, function(_h0/* s1opv */){
    return E(_gZ/* s1opu */);
  })));
},
_h1/* a65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_h2/* lvl25 */ = 18,
_h3/* a66 */ = function(_h4/* s1opz */){
  var _h5/* s1opA */ = new T(function(){
    return B(A1(_h4/* s1opz */,_h2/* Text.Read.Lex.lvl25 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_h1/* Text.Read.Lex.a65 */, function(_h6/* s1opB */){
    return E(_h5/* s1opA */);
  })));
},
_h7/* a67 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_h8/* lvl24 */ = 19,
_h9/* a68 */ = function(_ha/* s1opF */){
  var _hb/* s1opG */ = new T(function(){
    return B(A1(_ha/* s1opF */,_h8/* Text.Read.Lex.lvl24 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_h7/* Text.Read.Lex.a67 */, function(_hc/* s1opH */){
    return E(_hb/* s1opG */);
  })));
},
_hd/* a69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_he/* lvl23 */ = 20,
_hf/* a70 */ = function(_hg/* s1opL */){
  var _hh/* s1opM */ = new T(function(){
    return B(A1(_hg/* s1opL */,_he/* Text.Read.Lex.lvl23 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hd/* Text.Read.Lex.a69 */, function(_hi/* s1opN */){
    return E(_hh/* s1opM */);
  })));
},
_hj/* a71 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_hk/* lvl22 */ = 21,
_hl/* a72 */ = function(_hm/* s1opR */){
  var _hn/* s1opS */ = new T(function(){
    return B(A1(_hm/* s1opR */,_hk/* Text.Read.Lex.lvl22 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hj/* Text.Read.Lex.a71 */, function(_ho/* s1opT */){
    return E(_hn/* s1opS */);
  })));
},
_hp/* a73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_hq/* lvl21 */ = 22,
_hr/* a74 */ = function(_hs/* s1opX */){
  var _ht/* s1opY */ = new T(function(){
    return B(A1(_hs/* s1opX */,_hq/* Text.Read.Lex.lvl21 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hp/* Text.Read.Lex.a73 */, function(_hu/* s1opZ */){
    return E(_ht/* s1opY */);
  })));
},
_hv/* a75 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_hw/* lvl20 */ = 23,
_hx/* a76 */ = function(_hy/* s1oq3 */){
  var _hz/* s1oq4 */ = new T(function(){
    return B(A1(_hy/* s1oq3 */,_hw/* Text.Read.Lex.lvl20 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hv/* Text.Read.Lex.a75 */, function(_hA/* s1oq5 */){
    return E(_hz/* s1oq4 */);
  })));
},
_hB/* a77 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_hC/* lvl19 */ = 24,
_hD/* a78 */ = function(_hE/* s1oq9 */){
  var _hF/* s1oqa */ = new T(function(){
    return B(A1(_hE/* s1oq9 */,_hC/* Text.Read.Lex.lvl19 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hB/* Text.Read.Lex.a77 */, function(_hG/* s1oqb */){
    return E(_hF/* s1oqa */);
  })));
},
_hH/* a79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_hI/* lvl18 */ = 25,
_hJ/* a80 */ = function(_hK/* s1oqf */){
  var _hL/* s1oqg */ = new T(function(){
    return B(A1(_hK/* s1oqf */,_hI/* Text.Read.Lex.lvl18 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hH/* Text.Read.Lex.a79 */, function(_hM/* s1oqh */){
    return E(_hL/* s1oqg */);
  })));
},
_hN/* a81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_hO/* lvl17 */ = 26,
_hP/* a82 */ = function(_hQ/* s1oql */){
  var _hR/* s1oqm */ = new T(function(){
    return B(A1(_hQ/* s1oql */,_hO/* Text.Read.Lex.lvl17 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hN/* Text.Read.Lex.a81 */, function(_hS/* s1oqn */){
    return E(_hR/* s1oqm */);
  })));
},
_hT/* a83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_hU/* lvl16 */ = 27,
_hV/* a84 */ = function(_hW/* s1oqr */){
  var _hX/* s1oqs */ = new T(function(){
    return B(A1(_hW/* s1oqr */,_hU/* Text.Read.Lex.lvl16 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hT/* Text.Read.Lex.a83 */, function(_hY/* s1oqt */){
    return E(_hX/* s1oqs */);
  })));
},
_hZ/* a85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_i0/* lvl15 */ = 28,
_i1/* a86 */ = function(_i2/* s1oqx */){
  var _i3/* s1oqy */ = new T(function(){
    return B(A1(_i2/* s1oqx */,_i0/* Text.Read.Lex.lvl15 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_hZ/* Text.Read.Lex.a85 */, function(_i4/* s1oqz */){
    return E(_i3/* s1oqy */);
  })));
},
_i5/* a87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_i6/* lvl14 */ = 29,
_i7/* a88 */ = function(_i8/* s1oqD */){
  var _i9/* s1oqE */ = new T(function(){
    return B(A1(_i8/* s1oqD */,_i6/* Text.Read.Lex.lvl14 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_i5/* Text.Read.Lex.a87 */, function(_ia/* s1oqF */){
    return E(_i9/* s1oqE */);
  })));
},
_ib/* a89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_ic/* lvl13 */ = 30,
_id/* a90 */ = function(_ie/* s1oqJ */){
  var _if/* s1oqK */ = new T(function(){
    return B(A1(_ie/* s1oqJ */,_ic/* Text.Read.Lex.lvl13 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_ib/* Text.Read.Lex.a89 */, function(_ig/* s1oqL */){
    return E(_if/* s1oqK */);
  })));
},
_ih/* a91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_ii/* lvl12 */ = 31,
_ij/* a92 */ = function(_ik/* s1oqP */){
  var _il/* s1oqQ */ = new T(function(){
    return B(A1(_ik/* s1oqP */,_ii/* Text.Read.Lex.lvl12 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_ih/* Text.Read.Lex.a91 */, function(_im/* s1oqR */){
    return E(_il/* s1oqQ */);
  })));
},
_in/* a93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_io/* x */ = 32,
_ip/* a94 */ = function(_iq/* s1oqV */){
  var _ir/* s1oqW */ = new T(function(){
    return B(A1(_iq/* s1oqV */,_io/* Text.Read.Lex.x */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_in/* Text.Read.Lex.a93 */, function(_is/* s1oqX */){
    return E(_ir/* s1oqW */);
  })));
},
_it/* a95 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DEL"));
}),
_iu/* x1 */ = 127,
_iv/* a96 */ = function(_iw/* s1or1 */){
  var _ix/* s1or2 */ = new T(function(){
    return B(A1(_iw/* s1or1 */,_iu/* Text.Read.Lex.x1 */));
  });
  return new T1(1,B(_f3/* Text.ParserCombinators.ReadP.$wa6 */(_it/* Text.Read.Lex.a95 */, function(_iy/* s1or3 */){
    return E(_ix/* s1or2 */);
  })));
},
_iz/* lvl47 */ = new T2(1,_iv/* Text.Read.Lex.a96 */,_k/* GHC.Types.[] */),
_iA/* lvl48 */ = new T2(1,_ip/* Text.Read.Lex.a94 */,_iz/* Text.Read.Lex.lvl47 */),
_iB/* lvl49 */ = new T2(1,_ij/* Text.Read.Lex.a92 */,_iA/* Text.Read.Lex.lvl48 */),
_iC/* lvl50 */ = new T2(1,_id/* Text.Read.Lex.a90 */,_iB/* Text.Read.Lex.lvl49 */),
_iD/* lvl51 */ = new T2(1,_i7/* Text.Read.Lex.a88 */,_iC/* Text.Read.Lex.lvl50 */),
_iE/* lvl52 */ = new T2(1,_i1/* Text.Read.Lex.a86 */,_iD/* Text.Read.Lex.lvl51 */),
_iF/* lvl53 */ = new T2(1,_hV/* Text.Read.Lex.a84 */,_iE/* Text.Read.Lex.lvl52 */),
_iG/* lvl54 */ = new T2(1,_hP/* Text.Read.Lex.a82 */,_iF/* Text.Read.Lex.lvl53 */),
_iH/* lvl55 */ = new T2(1,_hJ/* Text.Read.Lex.a80 */,_iG/* Text.Read.Lex.lvl54 */),
_iI/* lvl56 */ = new T2(1,_hD/* Text.Read.Lex.a78 */,_iH/* Text.Read.Lex.lvl55 */),
_iJ/* lvl57 */ = new T2(1,_hx/* Text.Read.Lex.a76 */,_iI/* Text.Read.Lex.lvl56 */),
_iK/* lvl58 */ = new T2(1,_hr/* Text.Read.Lex.a74 */,_iJ/* Text.Read.Lex.lvl57 */),
_iL/* lvl59 */ = new T2(1,_hl/* Text.Read.Lex.a72 */,_iK/* Text.Read.Lex.lvl58 */),
_iM/* lvl60 */ = new T2(1,_hf/* Text.Read.Lex.a70 */,_iL/* Text.Read.Lex.lvl59 */),
_iN/* lvl61 */ = new T2(1,_h9/* Text.Read.Lex.a68 */,_iM/* Text.Read.Lex.lvl60 */),
_iO/* lvl62 */ = new T2(1,_h3/* Text.Read.Lex.a66 */,_iN/* Text.Read.Lex.lvl61 */),
_iP/* lvl63 */ = new T2(1,_gX/* Text.Read.Lex.a64 */,_iO/* Text.Read.Lex.lvl62 */),
_iQ/* lvl64 */ = new T2(1,_gR/* Text.Read.Lex.a62 */,_iP/* Text.Read.Lex.lvl63 */),
_iR/* lvl65 */ = new T2(1,_gL/* Text.Read.Lex.a60 */,_iQ/* Text.Read.Lex.lvl64 */),
_iS/* lvl66 */ = new T2(1,_gF/* Text.Read.Lex.a58 */,_iR/* Text.Read.Lex.lvl65 */),
_iT/* lvl67 */ = new T2(1,_gz/* Text.Read.Lex.a56 */,_iS/* Text.Read.Lex.lvl66 */),
_iU/* lvl68 */ = new T2(1,_gt/* Text.Read.Lex.a54 */,_iT/* Text.Read.Lex.lvl67 */),
_iV/* lvl69 */ = new T2(1,_gn/* Text.Read.Lex.a52 */,_iU/* Text.Read.Lex.lvl68 */),
_iW/* lvl70 */ = new T2(1,_gh/* Text.Read.Lex.a50 */,_iV/* Text.Read.Lex.lvl69 */),
_iX/* lvl71 */ = new T2(1,_gb/* Text.Read.Lex.a48 */,_iW/* Text.Read.Lex.lvl70 */),
_iY/* lvl72 */ = new T2(1,_g5/* Text.Read.Lex.a46 */,_iX/* Text.Read.Lex.lvl71 */),
_iZ/* lvl73 */ = new T2(1,_fZ/* Text.Read.Lex.a44 */,_iY/* Text.Read.Lex.lvl72 */),
_j0/* lvl74 */ = new T2(1,_fT/* Text.Read.Lex.a42 */,_iZ/* Text.Read.Lex.lvl73 */),
_j1/* lvl75 */ = new T2(1,_fN/* Text.Read.Lex.a40 */,_j0/* Text.Read.Lex.lvl74 */),
_j2/* lvl76 */ = new T2(1,_fH/* Text.Read.Lex.a38 */,_j1/* Text.Read.Lex.lvl75 */),
_j3/* lvl77 */ = new T2(1,_fB/* Text.Read.Lex.a36 */,_j2/* Text.Read.Lex.lvl76 */),
_j4/* lvl78 */ = new T2(1,_fv/* Text.Read.Lex.a34 */,_j3/* Text.Read.Lex.lvl77 */),
_j5/* lvl79 */ = new T2(1,_fr/* Text.Read.Lex.a32 */,_j4/* Text.Read.Lex.lvl78 */),
_j6/* lexAscii */ = new T(function(){
  return B(_eV/* Text.ParserCombinators.ReadP.choice */(_j5/* Text.Read.Lex.lvl79 */));
}),
_j7/* lvl10 */ = 34,
_j8/* lvl11 */ = new T1(0,1114111),
_j9/* lvl8 */ = 92,
_ja/* lvl9 */ = 39,
_jb/* lexChar2 */ = function(_jc/* s1or7 */){
  var _jd/* s1or8 */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_g4/* Text.Read.Lex.lvl7 */));
  }),
  _je/* s1or9 */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_ga/* Text.Read.Lex.lvl6 */));
  }),
  _jf/* s1ora */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_gg/* Text.Read.Lex.lvl2 */));
  }),
  _jg/* s1orb */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_gm/* Text.Read.Lex.lvl4 */));
  }),
  _jh/* s1orc */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_gs/* Text.Read.Lex.lvl1 */));
  }),
  _ji/* s1ord */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_gy/* Text.Read.Lex.lvl5 */));
  }),
  _jj/* s1ore */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_gE/* Text.Read.Lex.lvl3 */));
  }),
  _jk/* s1orf */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_j9/* Text.Read.Lex.lvl8 */));
  }),
  _jl/* s1org */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_ja/* Text.Read.Lex.lvl9 */));
  }),
  _jm/* s1orh */ = new T(function(){
    return B(A1(_jc/* s1or7 */,_j7/* Text.Read.Lex.lvl10 */));
  }),
  _jn/* s1osl */ = new T(function(){
    var _jo/* s1orE */ = function(_jp/* s1oro */){
      var _jq/* s1orp */ = new T(function(){
        return B(_dd/* GHC.Integer.Type.smallInteger */(E(_jp/* s1oro */)));
      }),
      _jr/* s1orB */ = function(_js/* s1ors */){
        var _jt/* s1ort */ = B(_dO/* Text.Read.Lex.valInteger */(_jq/* s1orp */, _js/* s1ors */));
        if(!B(_eL/* GHC.Integer.Type.leInteger */(_jt/* s1ort */, _j8/* Text.Read.Lex.lvl11 */))){
          return new T0(2);
        }else{
          return new F(function(){return A1(_jc/* s1or7 */,new T(function(){
            var _ju/* s1orv */ = B(_eI/* GHC.Integer.Type.integerToInt */(_jt/* s1ort */));
            if(_ju/* s1orv */>>>0>1114111){
              return B(_eG/* GHC.Char.chr2 */(_ju/* s1orv */));
            }else{
              return _ju/* s1orv */;
            }
          }));});
        }
      };
      return new T1(1,B(_bP/* Text.Read.Lex.$wa6 */(_jp/* s1oro */, _jr/* s1orB */)));
    },
    _jv/* s1osk */ = new T(function(){
      var _jw/* s1orI */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_ii/* Text.Read.Lex.lvl12 */));
      }),
      _jx/* s1orJ */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_ic/* Text.Read.Lex.lvl13 */));
      }),
      _jy/* s1orK */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_i6/* Text.Read.Lex.lvl14 */));
      }),
      _jz/* s1orL */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_i0/* Text.Read.Lex.lvl15 */));
      }),
      _jA/* s1orM */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hU/* Text.Read.Lex.lvl16 */));
      }),
      _jB/* s1orN */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hO/* Text.Read.Lex.lvl17 */));
      }),
      _jC/* s1orO */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hI/* Text.Read.Lex.lvl18 */));
      }),
      _jD/* s1orP */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hC/* Text.Read.Lex.lvl19 */));
      }),
      _jE/* s1orQ */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hw/* Text.Read.Lex.lvl20 */));
      }),
      _jF/* s1orR */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hq/* Text.Read.Lex.lvl21 */));
      }),
      _jG/* s1orS */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_hk/* Text.Read.Lex.lvl22 */));
      }),
      _jH/* s1orT */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_he/* Text.Read.Lex.lvl23 */));
      }),
      _jI/* s1orU */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_h8/* Text.Read.Lex.lvl24 */));
      }),
      _jJ/* s1orV */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_h2/* Text.Read.Lex.lvl25 */));
      }),
      _jK/* s1orW */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_gW/* Text.Read.Lex.lvl26 */));
      }),
      _jL/* s1orX */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_gQ/* Text.Read.Lex.lvl27 */));
      }),
      _jM/* s1orY */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_gK/* Text.Read.Lex.lvl28 */));
      }),
      _jN/* s1orZ */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fg/* Text.Read.Lex.lvl29 */));
      }),
      _jO/* s1os0 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fY/* Text.Read.Lex.lvl30 */));
      }),
      _jP/* s1os1 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fS/* Text.Read.Lex.lvl31 */));
      }),
      _jQ/* s1os2 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fM/* Text.Read.Lex.lvl32 */));
      }),
      _jR/* s1os3 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fG/* Text.Read.Lex.lvl33 */));
      }),
      _jS/* s1os4 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fA/* Text.Read.Lex.lvl34 */));
      }),
      _jT/* s1os5 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fm/* Text.Read.Lex.lvl35 */));
      }),
      _jU/* s1os6 */ = new T(function(){
        return B(A1(_jc/* s1or7 */,_fu/* Text.Read.Lex.lvl36 */));
      }),
      _jV/* s1os7 */ = function(_jW/* s1os8 */){
        switch(E(_jW/* s1os8 */)){
          case 64:
            return E(_jU/* s1os6 */);
          case 65:
            return E(_jT/* s1os5 */);
          case 66:
            return E(_jS/* s1os4 */);
          case 67:
            return E(_jR/* s1os3 */);
          case 68:
            return E(_jQ/* s1os2 */);
          case 69:
            return E(_jP/* s1os1 */);
          case 70:
            return E(_jO/* s1os0 */);
          case 71:
            return E(_jd/* s1or8 */);
          case 72:
            return E(_je/* s1or9 */);
          case 73:
            return E(_jf/* s1ora */);
          case 74:
            return E(_jg/* s1orb */);
          case 75:
            return E(_jh/* s1orc */);
          case 76:
            return E(_ji/* s1ord */);
          case 77:
            return E(_jj/* s1ore */);
          case 78:
            return E(_jN/* s1orZ */);
          case 79:
            return E(_jM/* s1orY */);
          case 80:
            return E(_jL/* s1orX */);
          case 81:
            return E(_jK/* s1orW */);
          case 82:
            return E(_jJ/* s1orV */);
          case 83:
            return E(_jI/* s1orU */);
          case 84:
            return E(_jH/* s1orT */);
          case 85:
            return E(_jG/* s1orS */);
          case 86:
            return E(_jF/* s1orR */);
          case 87:
            return E(_jE/* s1orQ */);
          case 88:
            return E(_jD/* s1orP */);
          case 89:
            return E(_jC/* s1orO */);
          case 90:
            return E(_jB/* s1orN */);
          case 91:
            return E(_jA/* s1orM */);
          case 92:
            return E(_jz/* s1orL */);
          case 93:
            return E(_jy/* s1orK */);
          case 94:
            return E(_jx/* s1orJ */);
          case 95:
            return E(_jw/* s1orI */);
          default:
            return new T0(2);
        }
      };
      return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_jX/* s1osd */){
        return (E(_jX/* s1osd */)==94) ? E(new T1(0,_jV/* s1os7 */)) : new T0(2);
      }), new T(function(){
        return B(A1(_j6/* Text.Read.Lex.lexAscii */,_jc/* s1or7 */));
      })));
    });
    return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_b6/* Text.ParserCombinators.ReadP.$wa */(_eC/* Text.Read.Lex.a4 */, _eE/* Text.Read.Lex.a5 */, _jo/* s1orE */))), _jv/* s1osk */));
  });
  return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_jY/* s1ori */){
    switch(E(_jY/* s1ori */)){
      case 34:
        return E(_jm/* s1orh */);
      case 39:
        return E(_jl/* s1org */);
      case 92:
        return E(_jk/* s1orf */);
      case 97:
        return E(_jd/* s1or8 */);
      case 98:
        return E(_je/* s1or9 */);
      case 102:
        return E(_ji/* s1ord */);
      case 110:
        return E(_jg/* s1orb */);
      case 114:
        return E(_jj/* s1ore */);
      case 116:
        return E(_jf/* s1ora */);
      case 118:
        return E(_jh/* s1orc */);
      default:
        return new T0(2);
    }
  }), _jn/* s1osl */);});
},
_jZ/* a */ = function(_k0/* s1iyn */){
  return new F(function(){return A1(_k0/* s1iyn */,_0/* GHC.Tuple.() */);});
},
_k1/* skipSpaces_skip */ = function(_k2/* s1iIB */){
  var _k3/* s1iIC */ = E(_k2/* s1iIB */);
  if(!_k3/* s1iIC */._){
    return E(_jZ/* Text.ParserCombinators.ReadP.a */);
  }else{
    var _k4/* s1iIF */ = E(_k3/* s1iIC */.a),
    _k5/* s1iIH */ = _k4/* s1iIF */>>>0,
    _k6/* s1iIJ */ = new T(function(){
      return B(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */(_k3/* s1iIC */.b));
    });
    if(_k5/* s1iIH */>887){
      var _k7/* s1iIO */ = u_iswspace/* EXTERNAL */(_k4/* s1iIF */);
      if(!E(_k7/* s1iIO */)){
        return E(_jZ/* Text.ParserCombinators.ReadP.a */);
      }else{
        var _k8/* s1iIW */ = function(_k9/* s1iIS */){
          var _ka/* s1iIT */ = new T(function(){
            return B(A1(_k6/* s1iIJ */,_k9/* s1iIS */));
          });
          return new T1(0,function(_kb/* s1iIU */){
            return E(_ka/* s1iIT */);
          });
        };
        return E(_k8/* s1iIW */);
      }
    }else{
      var _kc/* s1iIX */ = E(_k5/* s1iIH */);
      if(_kc/* s1iIX */==32){
        var _kd/* s1iJg */ = function(_ke/* s1iJc */){
          var _kf/* s1iJd */ = new T(function(){
            return B(A1(_k6/* s1iIJ */,_ke/* s1iJc */));
          });
          return new T1(0,function(_kg/* s1iJe */){
            return E(_kf/* s1iJd */);
          });
        };
        return E(_kd/* s1iJg */);
      }else{
        if(_kc/* s1iIX */-9>>>0>4){
          if(E(_kc/* s1iIX */)==160){
            var _kh/* s1iJ6 */ = function(_ki/* s1iJ2 */){
              var _kj/* s1iJ3 */ = new T(function(){
                return B(A1(_k6/* s1iIJ */,_ki/* s1iJ2 */));
              });
              return new T1(0,function(_kk/* s1iJ4 */){
                return E(_kj/* s1iJ3 */);
              });
            };
            return E(_kh/* s1iJ6 */);
          }else{
            return E(_jZ/* Text.ParserCombinators.ReadP.a */);
          }
        }else{
          var _kl/* s1iJb */ = function(_km/* s1iJ7 */){
            var _kn/* s1iJ8 */ = new T(function(){
              return B(A1(_k6/* s1iIJ */,_km/* s1iJ7 */));
            });
            return new T1(0,function(_ko/* s1iJ9 */){
              return E(_kn/* s1iJ8 */);
            });
          };
          return E(_kl/* s1iJb */);
        }
      }
    }
  }
},
_kp/* a97 */ = function(_kq/* s1osm */){
  var _kr/* s1osn */ = new T(function(){
    return B(_kp/* Text.Read.Lex.a97 */(_kq/* s1osm */));
  }),
  _ks/* s1oso */ = function(_kt/* s1osp */){
    return (E(_kt/* s1osp */)==92) ? E(_kr/* s1osn */) : new T0(2);
  },
  _ku/* s1osu */ = function(_kv/* s1osv */){
    return E(new T1(0,_ks/* s1oso */));
  },
  _kw/* s1osy */ = new T1(1,function(_kx/* s1osx */){
    return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_kx/* s1osx */, _ku/* s1osu */);});
  }),
  _ky/* s1osz */ = new T(function(){
    return B(_jb/* Text.Read.Lex.lexChar2 */(function(_kz/* s1osA */){
      return new F(function(){return A1(_kq/* s1osm */,new T2(0,_kz/* s1osA */,_8F/* GHC.Types.True */));});
    }));
  }),
  _kA/* s1osD */ = function(_kB/* s1osE */){
    var _kC/* s1osH */ = E(_kB/* s1osE */);
    if(_kC/* s1osH */==38){
      return E(_kr/* s1osn */);
    }else{
      var _kD/* s1osI */ = _kC/* s1osH */>>>0;
      if(_kD/* s1osI */>887){
        var _kE/* s1osO */ = u_iswspace/* EXTERNAL */(_kC/* s1osH */);
        return (E(_kE/* s1osO */)==0) ? new T0(2) : E(_kw/* s1osy */);
      }else{
        var _kF/* s1osS */ = E(_kD/* s1osI */);
        return (_kF/* s1osS */==32) ? E(_kw/* s1osy */) : (_kF/* s1osS */-9>>>0>4) ? (E(_kF/* s1osS */)==160) ? E(_kw/* s1osy */) : new T0(2) : E(_kw/* s1osy */);
      }
    }
  };
  return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_kG/* s1osY */){
    return (E(_kG/* s1osY */)==92) ? E(new T1(0,_kA/* s1osD */)) : new T0(2);
  }), new T1(0,function(_kH/* s1ot4 */){
    var _kI/* s1ot5 */ = E(_kH/* s1ot4 */);
    if(E(_kI/* s1ot5 */)==92){
      return E(_ky/* s1osz */);
    }else{
      return new F(function(){return A1(_kq/* s1osm */,new T2(0,_kI/* s1ot5 */,_4x/* GHC.Types.False */));});
    }
  }));});
},
_kJ/* a98 */ = function(_kK/* s1otb */, _kL/* s1otc */){
  var _kM/* s1otd */ = new T(function(){
    return B(A1(_kL/* s1otc */,new T1(1,new T(function(){
      return B(A1(_kK/* s1otb */,_k/* GHC.Types.[] */));
    }))));
  }),
  _kN/* s1otu */ = function(_kO/* s1otg */){
    var _kP/* s1oth */ = E(_kO/* s1otg */),
    _kQ/* s1otk */ = E(_kP/* s1oth */.a);
    if(E(_kQ/* s1otk */)==34){
      if(!E(_kP/* s1oth */.b)){
        return E(_kM/* s1otd */);
      }else{
        return new F(function(){return _kJ/* Text.Read.Lex.a98 */(function(_kR/* s1otr */){
          return new F(function(){return A1(_kK/* s1otb */,new T2(1,_kQ/* s1otk */,_kR/* s1otr */));});
        }, _kL/* s1otc */);});
      }
    }else{
      return new F(function(){return _kJ/* Text.Read.Lex.a98 */(function(_kS/* s1otn */){
        return new F(function(){return A1(_kK/* s1otb */,new T2(1,_kQ/* s1otk */,_kS/* s1otn */));});
      }, _kL/* s1otc */);});
    }
  };
  return new F(function(){return _kp/* Text.Read.Lex.a97 */(_kN/* s1otu */);});
},
_kT/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_\'"));
}),
_kU/* $wisIdfChar */ = function(_kV/* s1otE */){
  var _kW/* s1otH */ = u_iswalnum/* EXTERNAL */(_kV/* s1otE */);
  if(!E(_kW/* s1otH */)){
    return new F(function(){return _ep/* GHC.List.elem */(_aC/* GHC.Classes.$fEqChar */, _kV/* s1otE */, _kT/* Text.Read.Lex.lvl45 */);});
  }else{
    return true;
  }
},
_kX/* isIdfChar */ = function(_kY/* s1otM */){
  return new F(function(){return _kU/* Text.Read.Lex.$wisIdfChar */(E(_kY/* s1otM */));});
},
_kZ/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(",;()[]{}`"));
}),
_l0/* a7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("=>"));
}),
_l1/* a8 */ = new T2(1,_l0/* Text.Read.Lex.a7 */,_k/* GHC.Types.[] */),
_l2/* a9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("~"));
}),
_l3/* a10 */ = new T2(1,_l2/* Text.Read.Lex.a9 */,_l1/* Text.Read.Lex.a8 */),
_l4/* a11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("@"));
}),
_l5/* a12 */ = new T2(1,_l4/* Text.Read.Lex.a11 */,_l3/* Text.Read.Lex.a10 */),
_l6/* a13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("->"));
}),
_l7/* a14 */ = new T2(1,_l6/* Text.Read.Lex.a13 */,_l5/* Text.Read.Lex.a12 */),
_l8/* a15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<-"));
}),
_l9/* a16 */ = new T2(1,_l8/* Text.Read.Lex.a15 */,_l7/* Text.Read.Lex.a14 */),
_la/* a17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("|"));
}),
_lb/* a18 */ = new T2(1,_la/* Text.Read.Lex.a17 */,_l9/* Text.Read.Lex.a16 */),
_lc/* a19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\"));
}),
_ld/* a20 */ = new T2(1,_lc/* Text.Read.Lex.a19 */,_lb/* Text.Read.Lex.a18 */),
_le/* a21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_lf/* a22 */ = new T2(1,_le/* Text.Read.Lex.a21 */,_ld/* Text.Read.Lex.a20 */),
_lg/* a23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("::"));
}),
_lh/* a24 */ = new T2(1,_lg/* Text.Read.Lex.a23 */,_lf/* Text.Read.Lex.a22 */),
_li/* a25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".."));
}),
_lj/* reserved_ops */ = new T2(1,_li/* Text.Read.Lex.a25 */,_lh/* Text.Read.Lex.a24 */),
_lk/* expect2 */ = function(_ll/* s1otP */){
  var _lm/* s1otQ */ = new T(function(){
    return B(A1(_ll/* s1otP */,_bK/* Text.Read.Lex.EOF */));
  }),
  _ln/* s1ovk */ = new T(function(){
    var _lo/* s1otX */ = new T(function(){
      var _lp/* s1ou6 */ = function(_lq/* s1otY */){
        var _lr/* s1otZ */ = new T(function(){
          return B(A1(_ll/* s1otP */,new T1(0,_lq/* s1otY */)));
        });
        return new T1(0,function(_ls/* s1ou1 */){
          return (E(_ls/* s1ou1 */)==39) ? E(_lr/* s1otZ */) : new T0(2);
        });
      };
      return B(_jb/* Text.Read.Lex.lexChar2 */(_lp/* s1ou6 */));
    }),
    _lt/* s1ou7 */ = function(_lu/* s1ou8 */){
      var _lv/* s1ou9 */ = E(_lu/* s1ou8 */);
      switch(E(_lv/* s1ou9 */)){
        case 39:
          return new T0(2);
        case 92:
          return E(_lo/* s1otX */);
        default:
          var _lw/* s1ouc */ = new T(function(){
            return B(A1(_ll/* s1otP */,new T1(0,_lv/* s1ou9 */)));
          });
          return new T1(0,function(_lx/* s1oue */){
            return (E(_lx/* s1oue */)==39) ? E(_lw/* s1ouc */) : new T0(2);
          });
      }
    },
    _ly/* s1ovj */ = new T(function(){
      var _lz/* s1ouq */ = new T(function(){
        return B(_kJ/* Text.Read.Lex.a98 */(_bL/* GHC.Base.id */, _ll/* s1otP */));
      }),
      _lA/* s1ovi */ = new T(function(){
        var _lB/* s1ovh */ = new T(function(){
          var _lC/* s1ovg */ = new T(function(){
            var _lD/* s1ovb */ = function(_lE/* s1ouP */){
              var _lF/* s1ouQ */ = E(_lE/* s1ouP */),
              _lG/* s1ouU */ = u_iswalpha/* EXTERNAL */(_lF/* s1ouQ */);
              return (E(_lG/* s1ouU */)==0) ? (E(_lF/* s1ouQ */)==95) ? new T1(1,B(_bw/* Text.ParserCombinators.ReadP.$wa3 */(_kX/* Text.Read.Lex.isIdfChar */, function(_lH/* s1ov5 */){
                return new F(function(){return A1(_ll/* s1otP */,new T1(3,new T2(1,_lF/* s1ouQ */,_lH/* s1ov5 */)));});
              }))) : new T0(2) : new T1(1,B(_bw/* Text.ParserCombinators.ReadP.$wa3 */(_kX/* Text.Read.Lex.isIdfChar */, function(_lI/* s1ouY */){
                return new F(function(){return A1(_ll/* s1otP */,new T1(3,new T2(1,_lF/* s1ouQ */,_lI/* s1ouY */)));});
              })));
            };
            return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_lD/* s1ovb */), new T(function(){
              return new T1(1,B(_b6/* Text.ParserCombinators.ReadP.$wa */(_cK/* Text.Read.Lex.a2 */, _el/* Text.Read.Lex.a27 */, _ll/* s1otP */)));
            })));
          }),
          _lJ/* s1ouN */ = function(_lK/* s1ouD */){
            return (!B(_ep/* GHC.List.elem */(_aC/* GHC.Classes.$fEqChar */, _lK/* s1ouD */, _eu/* Text.Read.Lex.lvl44 */))) ? new T0(2) : new T1(1,B(_bw/* Text.ParserCombinators.ReadP.$wa3 */(_ev/* Text.Read.Lex.a6 */, function(_lL/* s1ouF */){
              var _lM/* s1ouG */ = new T2(1,_lK/* s1ouD */,_lL/* s1ouF */);
              if(!B(_ep/* GHC.List.elem */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, _lM/* s1ouG */, _lj/* Text.Read.Lex.reserved_ops */))){
                return new F(function(){return A1(_ll/* s1otP */,new T1(4,_lM/* s1ouG */));});
              }else{
                return new F(function(){return A1(_ll/* s1otP */,new T1(2,_lM/* s1ouG */));});
              }
            })));
          };
          return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_lJ/* s1ouN */), _lC/* s1ovg */));
        });
        return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_lN/* s1oux */){
          if(!B(_ep/* GHC.List.elem */(_aC/* GHC.Classes.$fEqChar */, _lN/* s1oux */, _kZ/* Text.Read.Lex.lvl43 */))){
            return new T0(2);
          }else{
            return new F(function(){return A1(_ll/* s1otP */,new T1(2,new T2(1,_lN/* s1oux */,_k/* GHC.Types.[] */)));});
          }
        }), _lB/* s1ovh */));
      });
      return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_lO/* s1our */){
        return (E(_lO/* s1our */)==34) ? E(_lz/* s1ouq */) : new T0(2);
      }), _lA/* s1ovi */));
    });
    return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_lP/* s1ouk */){
      return (E(_lP/* s1ouk */)==39) ? E(new T1(0,_lt/* s1ou7 */)) : new T0(2);
    }), _ly/* s1ovj */));
  });
  return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_lQ/* s1otR */){
    return (E(_lQ/* s1otR */)._==0) ? E(_lm/* s1otQ */) : new T0(2);
  }), _ln/* s1ovk */);});
},
_lR/* minPrec */ = 0,
_lS/* $wa3 */ = function(_lT/* s1viS */, _lU/* s1viT */){
  var _lV/* s1viU */ = new T(function(){
    var _lW/* s1viV */ = new T(function(){
      var _lX/* s1vj8 */ = function(_lY/* s1viW */){
        var _lZ/* s1viX */ = new T(function(){
          var _m0/* s1viY */ = new T(function(){
            return B(A1(_lU/* s1viT */,_lY/* s1viW */));
          });
          return B(_lk/* Text.Read.Lex.expect2 */(function(_m1/* s1viZ */){
            var _m2/* s1vj0 */ = E(_m1/* s1viZ */);
            return (_m2/* s1vj0 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_m2/* s1vj0 */.a, _av/* GHC.Read.$fRead(,)4 */))) ? new T0(2) : E(_m0/* s1viY */) : new T0(2);
          }));
        }),
        _m3/* s1vj4 */ = function(_m4/* s1vj5 */){
          return E(_lZ/* s1viX */);
        };
        return new T1(1,function(_m5/* s1vj6 */){
          return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_m5/* s1vj6 */, _m3/* s1vj4 */);});
        });
      };
      return B(A2(_lT/* s1viS */,_lR/* Text.ParserCombinators.ReadPrec.minPrec */, _lX/* s1vj8 */));
    });
    return B(_lk/* Text.Read.Lex.expect2 */(function(_m6/* s1vj9 */){
      var _m7/* s1vja */ = E(_m6/* s1vj9 */);
      return (_m7/* s1vja */._==2) ? (!B(_2n/* GHC.Base.eqString */(_m7/* s1vja */.a, _au/* GHC.Read.$fRead(,)3 */))) ? new T0(2) : E(_lW/* s1viV */) : new T0(2);
    }));
  }),
  _m8/* s1vje */ = function(_m9/* s1vjf */){
    return E(_lV/* s1viU */);
  };
  return function(_ma/* s1vjg */){
    return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_ma/* s1vjg */, _m8/* s1vje */);});
  };
},
_mb/* $fReadDouble10 */ = function(_mc/* s1vjn */, _md/* s1vjo */){
  var _me/* s1vjp */ = function(_mf/* s1vjq */){
    var _mg/* s1vjr */ = new T(function(){
      return B(A1(_mc/* s1vjn */,_mf/* s1vjq */));
    }),
    _mh/* s1vjx */ = function(_mi/* s1vjs */){
      return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_mg/* s1vjr */,_mi/* s1vjs */)), new T(function(){
        return new T1(1,B(_lS/* GHC.Read.$wa3 */(_me/* s1vjp */, _mi/* s1vjs */)));
      }));});
    };
    return E(_mh/* s1vjx */);
  },
  _mj/* s1vjy */ = new T(function(){
    return B(A1(_mc/* s1vjn */,_md/* s1vjo */));
  }),
  _mk/* s1vjE */ = function(_ml/* s1vjz */){
    return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_mj/* s1vjy */,_ml/* s1vjz */)), new T(function(){
      return new T1(1,B(_lS/* GHC.Read.$wa3 */(_me/* s1vjp */, _ml/* s1vjz */)));
    }));});
  };
  return E(_mk/* s1vjE */);
},
_mm/* $fReadInt3 */ = function(_mn/* s1vlT */, _mo/* s1vlU */){
  var _mp/* s1vmt */ = function(_mq/* s1vlV */, _mr/* s1vlW */){
    var _ms/* s1vlX */ = function(_mt/* s1vlY */){
      return new F(function(){return A1(_mr/* s1vlW */,new T(function(){
        return  -E(_mt/* s1vlY */);
      }));});
    },
    _mu/* s1vm5 */ = new T(function(){
      return B(_lk/* Text.Read.Lex.expect2 */(function(_mv/* s1vm4 */){
        return new F(function(){return A3(_mn/* s1vlT */,_mv/* s1vm4 */, _mq/* s1vlV */, _ms/* s1vlX */);});
      }));
    }),
    _mw/* s1vm6 */ = function(_mx/* s1vm7 */){
      return E(_mu/* s1vm5 */);
    },
    _my/* s1vm8 */ = function(_mz/* s1vm9 */){
      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_mz/* s1vm9 */, _mw/* s1vm6 */);});
    },
    _mA/* s1vmo */ = new T(function(){
      return B(_lk/* Text.Read.Lex.expect2 */(function(_mB/* s1vmc */){
        var _mC/* s1vmd */ = E(_mB/* s1vmc */);
        if(_mC/* s1vmd */._==4){
          var _mD/* s1vmf */ = E(_mC/* s1vmd */.a);
          if(!_mD/* s1vmf */._){
            return new F(function(){return A3(_mn/* s1vlT */,_mC/* s1vmd */, _mq/* s1vlV */, _mr/* s1vlW */);});
          }else{
            if(E(_mD/* s1vmf */.a)==45){
              if(!E(_mD/* s1vmf */.b)._){
                return E(new T1(1,_my/* s1vm8 */));
              }else{
                return new F(function(){return A3(_mn/* s1vlT */,_mC/* s1vmd */, _mq/* s1vlV */, _mr/* s1vlW */);});
              }
            }else{
              return new F(function(){return A3(_mn/* s1vlT */,_mC/* s1vmd */, _mq/* s1vlV */, _mr/* s1vlW */);});
            }
          }
        }else{
          return new F(function(){return A3(_mn/* s1vlT */,_mC/* s1vmd */, _mq/* s1vlV */, _mr/* s1vlW */);});
        }
      }));
    }),
    _mE/* s1vmp */ = function(_mF/* s1vmq */){
      return E(_mA/* s1vmo */);
    };
    return new T1(1,function(_mG/* s1vmr */){
      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_mG/* s1vmr */, _mE/* s1vmp */);});
    });
  };
  return new F(function(){return _mb/* GHC.Read.$fReadDouble10 */(_mp/* s1vmt */, _mo/* s1vlU */);});
},
_mH/* numberToInteger */ = function(_mI/* s1ojv */){
  var _mJ/* s1ojw */ = E(_mI/* s1ojv */);
  if(!_mJ/* s1ojw */._){
    var _mK/* s1ojy */ = _mJ/* s1ojw */.b,
    _mL/* s1ojF */ = new T(function(){
      return B(_dx/* Text.Read.Lex.numberToFixed_go */(new T(function(){
        return B(_dd/* GHC.Integer.Type.smallInteger */(E(_mJ/* s1ojw */.a)));
      }), new T(function(){
        return B(_d8/* GHC.List.$wlenAcc */(_mK/* s1ojy */, 0));
      },1), B(_8G/* GHC.Base.map */(_df/* Text.Read.Lex.numberToFixed2 */, _mK/* s1ojy */))));
    });
    return new T1(1,_mL/* s1ojF */);
  }else{
    return (E(_mJ/* s1ojw */.b)._==0) ? (E(_mJ/* s1ojw */.c)._==0) ? new T1(1,new T(function(){
      return B(_dO/* Text.Read.Lex.valInteger */(_d7/* Text.Read.Lex.numberToFixed1 */, _mJ/* s1ojw */.a));
    })) : __Z/* EXTERNAL */ : __Z/* EXTERNAL */;
  }
},
_mM/* pfail1 */ = function(_mN/* s1kH8 */, _mO/* s1kH9 */){
  return new T0(2);
},
_mP/* $fReadInt_$sconvertInt */ = function(_mQ/* s1vie */){
  var _mR/* s1vif */ = E(_mQ/* s1vie */);
  if(_mR/* s1vif */._==5){
    var _mS/* s1vih */ = B(_mH/* Text.Read.Lex.numberToInteger */(_mR/* s1vif */.a));
    if(!_mS/* s1vih */._){
      return E(_mM/* Text.ParserCombinators.ReadPrec.pfail1 */);
    }else{
      var _mT/* s1vij */ = new T(function(){
        return B(_eI/* GHC.Integer.Type.integerToInt */(_mS/* s1vih */.a));
      });
      return function(_mU/* s1vil */, _mV/* s1vim */){
        return new F(function(){return A1(_mV/* s1vim */,_mT/* s1vij */);});
      };
    }
  }else{
    return E(_mM/* Text.ParserCombinators.ReadPrec.pfail1 */);
  }
},
_mW/* readEither5 */ = function(_mX/* s2Rfe */){
  var _mY/* s2Rfg */ = function(_mZ/* s2Rfh */){
    return E(new T2(3,_mX/* s2Rfe */,_aX/* Text.ParserCombinators.ReadP.Fail */));
  };
  return new T1(1,function(_n0/* s2Rfi */){
    return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_n0/* s2Rfi */, _mY/* s2Rfg */);});
  });
},
_n1/* updateElementValue1 */ = new T(function(){
  return B(A3(_mm/* GHC.Read.$fReadInt3 */,_mP/* GHC.Read.$fReadInt_$sconvertInt */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _mW/* Text.Read.readEither5 */));
}),
_n2/* updateElementValue */ = function(_n3/* siRp */, _n4/* siRq */){
  var _n5/* siRr */ = E(_n3/* siRp */);
  switch(_n5/* siRr */._){
    case 1:
      return new T3(1,_n5/* siRr */.a,_n4/* siRq */,_n5/* siRr */.c);
    case 2:
      return new T3(2,_n5/* siRr */.a,_n4/* siRq */,_n5/* siRr */.c);
    case 3:
      return new T3(3,_n5/* siRr */.a,_n4/* siRq */,_n5/* siRr */.c);
    case 4:
      return new T4(4,_n5/* siRr */.a,new T(function(){
        var _n6/* siRG */ = B(_8k/* Text.Read.readEither6 */(B(_8r/* Text.ParserCombinators.ReadP.run */(_n1/* FormEngine.FormElement.Updating.updateElementValue1 */, _n4/* siRq */))));
        if(!_n6/* siRG */._){
          return __Z/* EXTERNAL */;
        }else{
          if(!E(_n6/* siRG */.b)._){
            return new T1(1,_n6/* siRG */.a);
          }else{
            return __Z/* EXTERNAL */;
          }
        }
      }),_n5/* siRr */.c,_n5/* siRr */.d);
    case 5:
      var _n7/* siSc */ = new T(function(){
        return B(_8G/* GHC.Base.map */(function(_n8/* siRQ */){
          var _n9/* siRR */ = E(_n8/* siRQ */);
          if(!_n9/* siRR */._){
            var _na/* siRU */ = E(_n9/* siRR */.a);
            return (_na/* siRU */._==0) ? (!B(_2n/* GHC.Base.eqString */(_na/* siRU */.a, _n4/* siRq */))) ? new T2(0,_na/* siRU */,_4x/* GHC.Types.False */) : new T2(0,_na/* siRU */,_8F/* GHC.Types.True */) : (!B(_2n/* GHC.Base.eqString */(_na/* siRU */.b, _n4/* siRq */))) ? new T2(0,_na/* siRU */,_4x/* GHC.Types.False */) : new T2(0,_na/* siRU */,_8F/* GHC.Types.True */);
          }else{
            var _nb/* siS3 */ = _n9/* siRR */.c,
            _nc/* siS4 */ = E(_n9/* siRR */.a);
            return (_nc/* siS4 */._==0) ? (!B(_2n/* GHC.Base.eqString */(_nc/* siS4 */.a, _n4/* siRq */))) ? new T3(1,_nc/* siS4 */,_4x/* GHC.Types.False */,_nb/* siS3 */) : new T3(1,_nc/* siS4 */,_8F/* GHC.Types.True */,_nb/* siS3 */) : (!B(_2n/* GHC.Base.eqString */(_nc/* siS4 */.b, _n4/* siRq */))) ? new T3(1,_nc/* siS4 */,_4x/* GHC.Types.False */,_nb/* siS3 */) : new T3(1,_nc/* siS4 */,_8F/* GHC.Types.True */,_nb/* siS3 */);
          }
        }, _n5/* siRr */.b));
      });
      return new T3(5,_n5/* siRr */.a,_n7/* siSc */,_n5/* siRr */.c);
    case 6:
      return new T3(6,_n5/* siRr */.a,new T(function(){
        if(!B(_2n/* GHC.Base.eqString */(_n4/* siRq */, _k/* GHC.Types.[] */))){
          return new T1(1,_n4/* siRq */);
        }else{
          return __Z/* EXTERNAL */;
        }
      }),_n5/* siRr */.c);
    default:
      return E(_n5/* siRr */);
  }
},
_nd/* identity2elementUpdated2 */ = function(_ne/* siSi */, _/* EXTERNAL */){
  var _nf/* siSk */ = E(_ne/* siSi */);
  switch(_nf/* siSk */._){
    case 0:
      var _ng/* siSB */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nh/* siSJ */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_ng/* siSB */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _ni/* siSN */ = String/* EXTERNAL */(_nh/* siSJ */);
          return fromJSStr/* EXTERNAL */(_ni/* siSN */);
        })));
      });
    case 1:
      var _nj/* siTb */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nk/* siTj */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nj/* siTb */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nl/* siTn */ = String/* EXTERNAL */(_nk/* siTj */);
          return fromJSStr/* EXTERNAL */(_nl/* siTn */);
        })));
      });
    case 2:
      var _nm/* siTL */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nn/* siTT */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nm/* siTL */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _no/* siTX */ = String/* EXTERNAL */(_nn/* siTT */);
          return fromJSStr/* EXTERNAL */(_no/* siTX */);
        })));
      });
    case 3:
      var _np/* siUl */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nq/* siUt */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_np/* siUl */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nr/* siUx */ = String/* EXTERNAL */(_nq/* siUt */);
          return fromJSStr/* EXTERNAL */(_nr/* siUx */);
        })));
      });
    case 4:
      var _ns/* siUF */ = _nf/* siSk */.a,
      _nt/* siUI */ = _nf/* siSk */.d,
      _nu/* siUL */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_ns/* siUF */)).b,
      _nv/* siUW */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(_nu/* siUL */)), _/* EXTERNAL */)),
      _nw/* siV4 */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nv/* siUW */)),
      _nx/* siV9 */ = B(_8c/* FormEngine.JQuery.getRadioValue1 */(new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(_nu/* siUL */)), _8j/* FormEngine.FormItem.nfiUnitId1 */));
      },1), _/* EXTERNAL */));
      return new T(function(){
        var _ny/* siVc */ = new T(function(){
          var _nz/* siVe */ = String/* EXTERNAL */(_nw/* siV4 */);
          return fromJSStr/* EXTERNAL */(_nz/* siVe */);
        }),
        _nA/* siVk */ = function(_nB/* siVl */){
          return new T4(4,_ns/* siUF */,new T(function(){
            var _nC/* siVn */ = B(_8k/* Text.Read.readEither6 */(B(_8r/* Text.ParserCombinators.ReadP.run */(_n1/* FormEngine.FormElement.Updating.updateElementValue1 */, _ny/* siVc */))));
            if(!_nC/* siVn */._){
              return __Z/* EXTERNAL */;
            }else{
              if(!E(_nC/* siVn */.b)._){
                return new T1(1,_nC/* siVn */.a);
              }else{
                return __Z/* EXTERNAL */;
              }
            }
          }),_4y/* GHC.Base.Nothing */,_nt/* siUI */);
        };
        if(!B(_2n/* GHC.Base.eqString */(_nx/* siV9 */, _8i/* FormEngine.FormElement.Updating.lvl2 */))){
          var _nD/* siVv */ = E(_nx/* siV9 */);
          if(!_nD/* siVv */._){
            return B(_nA/* siVk */(_/* EXTERNAL */));
          }else{
            return new T4(4,_ns/* siUF */,new T(function(){
              var _nE/* siVz */ = B(_8k/* Text.Read.readEither6 */(B(_8r/* Text.ParserCombinators.ReadP.run */(_n1/* FormEngine.FormElement.Updating.updateElementValue1 */, _ny/* siVc */))));
              if(!_nE/* siVz */._){
                return __Z/* EXTERNAL */;
              }else{
                if(!E(_nE/* siVz */.b)._){
                  return new T1(1,_nE/* siVz */.a);
                }else{
                  return __Z/* EXTERNAL */;
                }
              }
            }),new T1(1,_nD/* siVv */),_nt/* siUI */);
          }
        }else{
          return B(_nA/* siVk */(_/* EXTERNAL */));
        }
      });
    case 5:
      var _nF/* siVY */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nG/* siW6 */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nF/* siVY */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nH/* siWa */ = String/* EXTERNAL */(_nG/* siW6 */);
          return fromJSStr/* EXTERNAL */(_nH/* siWa */);
        })));
      });
    case 6:
      var _nI/* siWy */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nJ/* siWG */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nI/* siWy */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nK/* siWK */ = String/* EXTERNAL */(_nJ/* siWG */);
          return fromJSStr/* EXTERNAL */(_nK/* siWK */);
        })));
      });
    case 7:
      var _nL/* siX8 */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nM/* siXg */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nL/* siX8 */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nN/* siXk */ = String/* EXTERNAL */(_nM/* siXg */);
          return fromJSStr/* EXTERNAL */(_nN/* siXk */);
        })));
      });
    case 8:
      var _nO/* siXJ */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nP/* siXR */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nO/* siXJ */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nQ/* siXV */ = String/* EXTERNAL */(_nP/* siXR */);
          return fromJSStr/* EXTERNAL */(_nQ/* siXV */);
        })));
      });
    case 9:
      var _nR/* siYj */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nS/* siYr */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nR/* siYj */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nT/* siYv */ = String/* EXTERNAL */(_nS/* siYr */);
          return fromJSStr/* EXTERNAL */(_nT/* siYv */);
        })));
      });
    case 10:
      var _nU/* siYS */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nV/* siZ0 */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nU/* siYS */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nW/* siZ4 */ = String/* EXTERNAL */(_nV/* siZ0 */);
          return fromJSStr/* EXTERNAL */(_nW/* siZ4 */);
        })));
      });
    default:
      var _nX/* siZr */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_nf/* siSk */.a)).b)), _/* EXTERNAL */)),
      _nY/* siZz */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_nX/* siZr */));
      return new T(function(){
        return B(_n2/* FormEngine.FormElement.Updating.updateElementValue */(_nf/* siSk */, new T(function(){
          var _nZ/* siZD */ = String/* EXTERNAL */(_nY/* siZz */);
          return fromJSStr/* EXTERNAL */(_nZ/* siZD */);
        })));
      });
  }
},
_o0/* identity2elementUpdated3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" does not exist"));
}),
_o1/* identity2elementUpdated4 */ = new T2(1,_5f/* GHC.Show.shows5 */,_k/* GHC.Types.[] */),
_o2/* $wa */ = function(_o3/* sj0m */, _o4/* sj0n */, _/* EXTERNAL */){
  var _o5/* sj0p */ = B(_7Z/* FormEngine.FormElement.Updating.identity2element' */(_o3/* sj0m */, _o4/* sj0n */));
  if(!_o5/* sj0p */._){
    var _o6/* sj0s */ = new T(function(){
      return B(_7/* GHC.Base.++ */(new T2(1,_5f/* GHC.Show.shows5 */,new T(function(){
        return B(_7i/* GHC.Show.showLitString */(_o3/* sj0m */, _o1/* FormEngine.FormElement.Updating.identity2elementUpdated4 */));
      })), _o0/* FormEngine.FormElement.Updating.identity2elementUpdated3 */));
    }),
    _o7/* sj0u */ = B(_3/* FormEngine.JQuery.errorIO1 */(B(unAppCStr/* EXTERNAL */("identity2elementUpdated: element with identity=", _o6/* sj0s */)), _/* EXTERNAL */));
    return _4y/* GHC.Base.Nothing */;
  }else{
    var _o8/* sj0y */ = B(_nd/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_o5/* sj0p */.a, _/* EXTERNAL */));
    return new T1(1,_o8/* sj0y */);
  }
},
_o9/* setVal2 */ = "(function (val, jq) { jq.val(val).change(); return jq; })",
_oa/* $wa35 */ = function(_ob/* skj1 */, _oc/* skj2 */, _/* EXTERNAL */){
  var _od/* skjc */ = eval/* EXTERNAL */(E(_o9/* FormEngine.JQuery.setVal2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_od/* skjc */), toJSStr/* EXTERNAL */(E(_ob/* skj1 */)), _oc/* skj2 */);});
},
_oe/* $fExceptionRecSelError_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RecSelError"));
}),
_of/* $fExceptionRecSelError_wild */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_8K/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_8L/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_oe/* Control.Exception.Base.$fExceptionRecSelError_ww4 */),
_og/* $fExceptionRecSelError2 */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_of/* Control.Exception.Base.$fExceptionRecSelError_wild */,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */),
_oh/* $fExceptionRecSelError1 */ = function(_oi/* s4nv0 */){
  return E(_og/* Control.Exception.Base.$fExceptionRecSelError2 */);
},
_oj/* $fExceptionRecSelError_$cfromException */ = function(_ok/* s4nvr */){
  var _ol/* s4nvs */ = E(_ok/* s4nvr */);
  return new F(function(){return _8T/* Data.Typeable.cast */(B(_8R/* GHC.Exception.$p1Exception */(_ol/* s4nvs */.a)), _oh/* Control.Exception.Base.$fExceptionRecSelError1 */, _ol/* s4nvs */.b);});
},
_om/* $fExceptionRecSelError_$cshow */ = function(_on/* s4nvj */){
  return E(E(_on/* s4nvj */).a);
},
_oo/* $fExceptionRecSelError_$ctoException */ = function(_97/* B1 */){
  return new T2(0,_op/* Control.Exception.Base.$fExceptionRecSelError */,_97/* B1 */);
},
_oq/* $fShowRecSelError1 */ = function(_or/* s4nqO */, _os/* s4nqP */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_or/* s4nqO */).a, _os/* s4nqP */);});
},
_ot/* $fShowRecSelError_$cshowList */ = function(_ou/* s4nvh */, _ov/* s4nvi */){
  return new F(function(){return _5s/* GHC.Show.showList__ */(_oq/* Control.Exception.Base.$fShowRecSelError1 */, _ou/* s4nvh */, _ov/* s4nvi */);});
},
_ow/* $fShowRecSelError_$cshowsPrec */ = function(_ox/* s4nvm */, _oy/* s4nvn */, _oz/* s4nvo */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_oy/* s4nvn */).a, _oz/* s4nvo */);});
},
_oA/* $fShowRecSelError */ = new T3(0,_ow/* Control.Exception.Base.$fShowRecSelError_$cshowsPrec */,_om/* Control.Exception.Base.$fExceptionRecSelError_$cshow */,_ot/* Control.Exception.Base.$fShowRecSelError_$cshowList */),
_op/* $fExceptionRecSelError */ = new T(function(){
  return new T5(0,_oh/* Control.Exception.Base.$fExceptionRecSelError1 */,_oA/* Control.Exception.Base.$fShowRecSelError */,_oo/* Control.Exception.Base.$fExceptionRecSelError_$ctoException */,_oj/* Control.Exception.Base.$fExceptionRecSelError_$cfromException */,_om/* Control.Exception.Base.$fExceptionRecSelError_$cshow */);
}),
_oB/* recSelError */ = function(_oC/* s4nwW */){
  var _oD/* s4nwY */ = new T(function(){
    return B(unAppCStr/* EXTERNAL */("No match in record selector ", new T(function(){
      return B(unCStr/* EXTERNAL */(_oC/* s4nwW */));
    })));
  });
  return new F(function(){return _9q/* GHC.Exception.throw1 */(new T1(0,_oD/* s4nwY */), _op/* Control.Exception.Base.$fExceptionRecSelError */);});
},
_oE/* neMaybeValue1 */ = new T(function(){
  return B(_oB/* Control.Exception.Base.recSelError */("neMaybeValue"));
}),
_oF/* $wgo */ = function(_oG/* sj0P */, _oH/* sj0Q */){
  while(1){
    var _oI/* sj0R */ = E(_oG/* sj0P */);
    if(!_oI/* sj0R */._){
      return E(_oH/* sj0Q */);
    }else{
      var _oJ/* sj0T */ = _oI/* sj0R */.b,
      _oK/* sj0U */ = E(_oI/* sj0R */.a);
      if(_oK/* sj0U */._==4){
        var _oL/* sj10 */ = E(_oK/* sj0U */.b);
        if(!_oL/* sj10 */._){
          _oG/* sj0P */ = _oJ/* sj0T */;
          continue;
        }else{
          var _oM/*  sj0Q */ = _oH/* sj0Q */+E(_oL/* sj10 */.a)|0;
          _oG/* sj0P */ = _oJ/* sj0T */;
          _oH/* sj0Q */ = _oM/*  sj0Q */;
          continue;
        }
      }else{
        return E(_oE/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
      }
    }
  }
},
_oN/* int2Float */ = function(_oO/* sc58 */){
  return E(_oO/* sc58 */);
},
_oP/* numberElem2TB1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_oQ/* numberElem2TB2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_oR/* numberElem2TB3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_oS/* numberElem2TB4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_oT/* numberElem2TB */ = function(_oU/* sc38 */){
  var _oV/* sc39 */ = E(_oU/* sc38 */);
  if(_oV/* sc39 */._==4){
    var _oW/* sc3b */ = _oV/* sc39 */.b,
    _oX/* sc3e */ = E(_oV/* sc39 */.c);
    if(!_oX/* sc3e */._){
      return __Z/* EXTERNAL */;
    }else{
      var _oY/* sc3f */ = _oX/* sc3e */.a;
      if(!B(_2n/* GHC.Base.eqString */(_oY/* sc3f */, _oS/* FormEngine.FormElement.FormElement.numberElem2TB4 */))){
        if(!B(_2n/* GHC.Base.eqString */(_oY/* sc3f */, _oR/* FormEngine.FormElement.FormElement.numberElem2TB3 */))){
          if(!B(_2n/* GHC.Base.eqString */(_oY/* sc3f */, _oQ/* FormEngine.FormElement.FormElement.numberElem2TB2 */))){
            if(!B(_2n/* GHC.Base.eqString */(_oY/* sc3f */, _oP/* FormEngine.FormElement.FormElement.numberElem2TB1 */))){
              return __Z/* EXTERNAL */;
            }else{
              var _oZ/* sc3k */ = E(_oW/* sc3b */);
              return (_oZ/* sc3k */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
                return B(_oN/* GHC.Float.RealFracMethods.int2Float */(_oZ/* sc3k */.a));
              }));
            }
          }else{
            var _p0/* sc3n */ = E(_oW/* sc3b */);
            return (_p0/* sc3n */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
              return E(_p0/* sc3n */.a)*1000;
            }));
          }
        }else{
          var _p1/* sc3u */ = E(_oW/* sc3b */);
          return (_p1/* sc3u */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
            return E(_p1/* sc3u */.a)*1.0e-6;
          }));
        }
      }else{
        var _p2/* sc3B */ = E(_oW/* sc3b */);
        return (_p2/* sc3B */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
          return E(_p2/* sc3B */.a)*1.0e-3;
        }));
      }
    }
  }else{
    return __Z/* EXTERNAL */;
  }
},
_p3/* $wgo1 */ = function(_p4/* sj1b */, _p5/* sj1c */){
  while(1){
    var _p6/* sj1d */ = E(_p4/* sj1b */);
    if(!_p6/* sj1d */._){
      return E(_p5/* sj1c */);
    }else{
      var _p7/* sj1f */ = _p6/* sj1d */.b,
      _p8/* sj1g */ = B(_oT/* FormEngine.FormElement.FormElement.numberElem2TB */(_p6/* sj1d */.a));
      if(!_p8/* sj1g */._){
        _p4/* sj1b */ = _p7/* sj1f */;
        continue;
      }else{
        var _p9/*  sj1c */ = _p5/* sj1c */+E(_p8/* sj1g */.a);
        _p4/* sj1b */ = _p7/* sj1f */;
        _p5/* sj1c */ = _p9/*  sj1c */;
        continue;
      }
    }
  }
},
_pa/* catMaybes1 */ = function(_pb/*  s7rA */){
  while(1){
    var _pc/*  catMaybes1 */ = B((function(_pd/* s7rA */){
      var _pe/* s7rB */ = E(_pd/* s7rA */);
      if(!_pe/* s7rB */._){
        return __Z/* EXTERNAL */;
      }else{
        var _pf/* s7rD */ = _pe/* s7rB */.b,
        _pg/* s7rE */ = E(_pe/* s7rB */.a);
        if(!_pg/* s7rE */._){
          _pb/*  s7rA */ = _pf/* s7rD */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_pg/* s7rE */.a,new T(function(){
            return B(_pa/* Data.Maybe.catMaybes1 */(_pf/* s7rD */));
          }));
        }
      }
    })(_pb/*  s7rA */));
    if(_pc/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _pc/*  catMaybes1 */;
    }
  }
},
_ph/* disableJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("true"));
}),
_pi/* disableJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("readonly"));
}),
_pj/* disableJq6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#eee"));
}),
_pk/* disableJq7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("background-color"));
}),
_pl/* elementId */ = function(_pm/* sbNm */){
  return new F(function(){return _27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pm/* sbNm */)))).b);});
},
_pn/* go */ = function(_po/* sj0J */){
  while(1){
    var _pp/* sj0K */ = E(_po/* sj0J */);
    if(!_pp/* sj0K */._){
      return false;
    }else{
      if(!E(_pp/* sj0K */.a)._){
        return true;
      }else{
        _po/* sj0J */ = _pp/* sj0K */.b;
        continue;
      }
    }
  }
},
_pq/* go1 */ = function(_pr/* sj15 */){
  while(1){
    var _ps/* sj16 */ = E(_pr/* sj15 */);
    if(!_ps/* sj16 */._){
      return false;
    }else{
      if(!E(_ps/* sj16 */.a)._){
        return true;
      }else{
        _pr/* sj15 */ = _ps/* sj16 */.b;
        continue;
      }
    }
  }
},
_pt/* selectIn2 */ = "(function (elId, context) { return $(elId, context); })",
_pu/* $wa18 */ = function(_pv/* skmv */, _pw/* skmw */, _/* EXTERNAL */){
  var _px/* skmG */ = eval/* EXTERNAL */(E(_pt/* FormEngine.JQuery.selectIn2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_px/* skmG */), toJSStr/* EXTERNAL */(E(_pv/* skmv */)), _pw/* skmw */);});
},
_py/* flagPlaceId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_flagPlaceId"));
}),
_pz/* flagPlaceId */ = function(_pA/* sft4 */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pA/* sft4 */)))).b)), _py/* FormEngine.FormElement.Identifiers.flagPlaceId1 */);});
},
_pB/* inputFieldUpdate3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".validity-flag"));
}),
_pC/* inputFieldUpdate4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_pD/* invalidImg */ = function(_pE/* seb3 */){
  return E(E(_pE/* seb3 */).c);
},
_pF/* removeJq_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { var p = jq.parent(); jq.remove(); return p; })");
}),
_pG/* validImg */ = function(_pH/* seb8 */){
  return E(E(_pH/* seb8 */).b);
},
_pI/* inputFieldUpdate2 */ = function(_pJ/* siQs */, _pK/* siQt */, _pL/* siQu */, _/* EXTERNAL */){
  var _pM/* siQy */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_pC/* FormEngine.FormElement.Updating.inputFieldUpdate4 */, new T(function(){
    return B(_pz/* FormEngine.FormElement.Identifiers.flagPlaceId */(_pJ/* siQs */));
  },1))), _/* EXTERNAL */)),
  _pN/* siQB */ = E(_pM/* siQy */),
  _pO/* siQD */ = B(_pu/* FormEngine.JQuery.$wa18 */(_pB/* FormEngine.FormElement.Updating.inputFieldUpdate3 */, _pN/* siQB */, _/* EXTERNAL */)),
  _pP/* siQL */ = __app1/* EXTERNAL */(E(_pF/* FormEngine.JQuery.removeJq_f1 */), E(_pO/* siQD */));
  if(!E(_pL/* siQu */)){
    if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pJ/* siQs */)))).j)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _pQ/* siR4 */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_pD/* FormEngine.FormContext.invalidImg */(_pK/* siQt */)), _pN/* siQB */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }else{
    if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pJ/* siQs */)))).j)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _pR/* siRm */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_pG/* FormEngine.FormContext.validImg */(_pK/* siQt */)), _pN/* siQB */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }
},
_pS/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rule application did not unify: "));
}),
_pT/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" @"));
}),
_pU/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid operand in "));
}),
_pV/* selectByIdentity2 */ = "(function (identity) { return $(\'[identity=\"\' + identity + \'\"]\'); })",
_pW/* selectByIdentity1 */ = function(_pX/* sk9a */, _/* EXTERNAL */){
  var _pY/* sk9k */ = eval/* EXTERNAL */(E(_pV/* FormEngine.JQuery.selectByIdentity2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_pY/* sk9k */), toJSStr/* EXTERNAL */(E(_pX/* sk9a */)));});
},
_pZ/* applyRule1 */ = function(_q0/* sj1l */, _q1/* sj1m */, _q2/* sj1n */, _/* EXTERNAL */){
  var _q3/* sj1p */ = function(_/* EXTERNAL */){
    var _q4/* sj1r */ = E(_q2/* sj1n */);
    switch(_q4/* sj1r */._){
      case 2:
        var _q5/* sj1z */ = B(_pW/* FormEngine.JQuery.selectByIdentity1 */(_q4/* sj1r */.a, _/* EXTERNAL */)),
        _q6/* sj1H */ = __app1/* EXTERNAL */(E(_8b/* FormEngine.JQuery.getRadioValue_f1 */), E(_q5/* sj1z */)),
        _q7/* sj1K */ = B(_pW/* FormEngine.JQuery.selectByIdentity1 */(_q4/* sj1r */.b, _/* EXTERNAL */)),
        _q8/* sj1O */ = String/* EXTERNAL */(_q6/* sj1H */),
        _q9/* sj1X */ = B(_oa/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_q8/* sj1O */), E(_q7/* sj1K */), _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 3:
        var _qa/* sj21 */ = B(_8C/* FormEngine.JQuery.selectByName1 */(B(_pl/* FormEngine.FormElement.FormElement.elementId */(_q0/* sj1l */)), _/* EXTERNAL */)),
        _qb/* sj24 */ = E(_qa/* sj21 */),
        _qc/* sj26 */ = B(_K/* FormEngine.JQuery.$wa2 */(_pk/* FormEngine.JQuery.disableJq7 */, _pj/* FormEngine.JQuery.disableJq6 */, _qb/* sj24 */, _/* EXTERNAL */)),
        _qd/* sj29 */ = B(_u/* FormEngine.JQuery.$wa6 */(_pi/* FormEngine.JQuery.disableJq3 */, _ph/* FormEngine.JQuery.disableJq2 */, _qb/* sj24 */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 4:
        var _qe/* sj2d */ = B(_nd/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_q0/* sj1l */, _/* EXTERNAL */)),
        _qf/* sj2g */ = E(_qe/* sj2d */);
        if(_qf/* sj2g */._==4){
          var _qg/* sj2m */ = E(_qf/* sj2g */.b);
          if(!_qg/* sj2m */._){
            return new F(function(){return _pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_qf/* sj2g */, _q1/* sj1m */, _4x/* GHC.Types.False */, _/* EXTERNAL */);});
          }else{
            return new F(function(){return _pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_qf/* sj2g */, _q1/* sj1m */, new T(function(){
              return B(A1(_q4/* sj1r */.a,_qg/* sj2m */.a));
            },1), _/* EXTERNAL */);});
          }
        }else{
          return E(_oE/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
        }
        break;
      default:
        var _qh/* sj1v */ = new T(function(){
          var _qi/* sj1u */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_pT/* FormEngine.FormElement.Updating.lvl4 */, new T(function(){
              return B(_55/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_q0/* sj1l */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(B(_7Q/* FormEngine.FormItem.$fShowFormRule_$cshow */(_q4/* sj1r */)), _qi/* sj1u */));
        },1);
        return new F(function(){return _3/* FormEngine.JQuery.errorIO1 */(B(_7/* GHC.Base.++ */(_pS/* FormEngine.FormElement.Updating.lvl3 */, _qh/* sj1v */)), _/* EXTERNAL */);});
    }
  };
  if(E(_q0/* sj1l */)._==4){
    var _qj/* sj2u */ = E(_q2/* sj1n */);
    switch(_qj/* sj2u */._){
      case 0:
        var _qk/* sj2x */ = function(_/* EXTERNAL */, _ql/* sj2z */){
          if(!B(_pn/* FormEngine.FormElement.Updating.go */(_ql/* sj2z */))){
            var _qm/* sj2B */ = B(_pW/* FormEngine.JQuery.selectByIdentity1 */(_qj/* sj2u */.b, _/* EXTERNAL */)),
            _qn/* sj2J */ = B(_oa/* FormEngine.JQuery.$wa35 */(B(_1M/* GHC.Show.$wshowSignedInt */(0, B(_oF/* FormEngine.FormElement.Updating.$wgo */(B(_pa/* Data.Maybe.catMaybes1 */(_ql/* sj2z */)), 0)), _k/* GHC.Types.[] */)), E(_qm/* sj2B */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _qo/* sj2O */ = B(_3/* FormEngine.JQuery.errorIO1 */(B(_7/* GHC.Base.++ */(_pU/* FormEngine.FormElement.Updating.lvl5 */, new T(function(){
              return B(_7Q/* FormEngine.FormItem.$fShowFormRule_$cshow */(_qj/* sj2u */));
            },1))), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        },
        _qp/* sj2R */ = E(_qj/* sj2u */.a);
        if(!_qp/* sj2R */._){
          return new F(function(){return _qk/* sj2x */(_/* EXTERNAL */, _k/* GHC.Types.[] */);});
        }else{
          var _qq/* sj2V */ = E(_q1/* sj1m */).a,
          _qr/* sj2Y */ = B(_o2/* FormEngine.FormElement.Updating.$wa */(_qp/* sj2R */.a, _qq/* sj2V */, _/* EXTERNAL */)),
          _qs/* sj31 */ = function(_qt/* sj32 */, _/* EXTERNAL */){
            var _qu/* sj34 */ = E(_qt/* sj32 */);
            if(!_qu/* sj34 */._){
              return _k/* GHC.Types.[] */;
            }else{
              var _qv/* sj37 */ = B(_o2/* FormEngine.FormElement.Updating.$wa */(_qu/* sj34 */.a, _qq/* sj2V */, _/* EXTERNAL */)),
              _qw/* sj3a */ = B(_qs/* sj31 */(_qu/* sj34 */.b, _/* EXTERNAL */));
              return new T2(1,_qv/* sj37 */,_qw/* sj3a */);
            }
          },
          _qx/* sj3e */ = B(_qs/* sj31 */(_qp/* sj2R */.b, _/* EXTERNAL */));
          return new F(function(){return _qk/* sj2x */(_/* EXTERNAL */, new T2(1,_qr/* sj2Y */,_qx/* sj3e */));});
        }
        break;
      case 1:
        var _qy/* sj3k */ = function(_/* EXTERNAL */, _qz/* sj3m */){
          if(!B(_pq/* FormEngine.FormElement.Updating.go1 */(_qz/* sj3m */))){
            var _qA/* sj3o */ = B(_pW/* FormEngine.JQuery.selectByIdentity1 */(_qj/* sj2u */.b, _/* EXTERNAL */)),
            _qB/* sj3u */ = jsShow/* EXTERNAL */(B(_p3/* FormEngine.FormElement.Updating.$wgo1 */(B(_pa/* Data.Maybe.catMaybes1 */(_qz/* sj3m */)), 0))),
            _qC/* sj3B */ = B(_oa/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_qB/* sj3u */), E(_qA/* sj3o */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            return _0/* GHC.Tuple.() */;
          }
        },
        _qD/* sj3E */ = E(_qj/* sj2u */.a);
        if(!_qD/* sj3E */._){
          return new F(function(){return _qy/* sj3k */(_/* EXTERNAL */, _k/* GHC.Types.[] */);});
        }else{
          var _qE/* sj3I */ = E(_q1/* sj1m */).a,
          _qF/* sj3L */ = B(_o2/* FormEngine.FormElement.Updating.$wa */(_qD/* sj3E */.a, _qE/* sj3I */, _/* EXTERNAL */)),
          _qG/* sj3O */ = function(_qH/* sj3P */, _/* EXTERNAL */){
            var _qI/* sj3R */ = E(_qH/* sj3P */);
            if(!_qI/* sj3R */._){
              return _k/* GHC.Types.[] */;
            }else{
              var _qJ/* sj3U */ = B(_o2/* FormEngine.FormElement.Updating.$wa */(_qI/* sj3R */.a, _qE/* sj3I */, _/* EXTERNAL */)),
              _qK/* sj3X */ = B(_qG/* sj3O */(_qI/* sj3R */.b, _/* EXTERNAL */));
              return new T2(1,_qJ/* sj3U */,_qK/* sj3X */);
            }
          },
          _qL/* sj41 */ = B(_qG/* sj3O */(_qD/* sj3E */.b, _/* EXTERNAL */));
          return new F(function(){return _qy/* sj3k */(_/* EXTERNAL */, new T2(1,_qF/* sj3L */,_qL/* sj41 */));});
        }
        break;
      default:
        return new F(function(){return _q3/* sj1p */(_/* EXTERNAL */);});
    }
  }else{
    return new F(function(){return _q3/* sj1p */(_/* EXTERNAL */);});
  }
},
_qM/* applyRules1 */ = function(_qN/* sj45 */, _qO/* sj46 */, _/* EXTERNAL */){
  var _qP/* sj4l */ = function(_qQ/* sj4m */, _/* EXTERNAL */){
    while(1){
      var _qR/* sj4o */ = E(_qQ/* sj4m */);
      if(!_qR/* sj4o */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _qS/* sj4r */ = B(_pZ/* FormEngine.FormElement.Updating.applyRule1 */(_qN/* sj45 */, _qO/* sj46 */, _qR/* sj4o */.a, _/* EXTERNAL */));
        _qQ/* sj4m */ = _qR/* sj4o */.b;
        continue;
      }
    }
  };
  return new F(function(){return _qP/* sj4l */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_qN/* sj45 */)))).k, _/* EXTERNAL */);});
},
_qT/* isJust */ = function(_qU/* s7rZ */){
  return (E(_qU/* s7rZ */)._==0) ? false : true;
},
_qV/* nfiUnit1 */ = new T(function(){
  return B(_oB/* Control.Exception.Base.recSelError */("nfiUnit"));
}),
_qW/* go */ = function(_qX/* seBF */){
  while(1){
    var _qY/* seBG */ = E(_qX/* seBF */);
    if(!_qY/* seBG */._){
      return true;
    }else{
      if(!E(_qY/* seBG */.a)){
        return false;
      }else{
        _qX/* seBF */ = _qY/* seBG */.b;
        continue;
      }
    }
  }
},
_qZ/* validateElement_go */ = function(_r0/* seBo */){
  while(1){
    var _r1/* seBp */ = E(_r0/* seBo */);
    if(!_r1/* seBp */._){
      return false;
    }else{
      var _r2/* seBr */ = _r1/* seBp */.b,
      _r3/* seBs */ = E(_r1/* seBp */.a);
      if(!_r3/* seBs */._){
        if(!E(_r3/* seBs */.b)){
          _r0/* seBo */ = _r2/* seBr */;
          continue;
        }else{
          return true;
        }
      }else{
        if(!E(_r3/* seBs */.b)){
          _r0/* seBo */ = _r2/* seBr */;
          continue;
        }else{
          return true;
        }
      }
    }
  }
},
_r4/* validateElement_go1 */ = function(_r5/* seBA */){
  while(1){
    var _r6/* seBB */ = E(_r5/* seBA */);
    if(!_r6/* seBB */._){
      return true;
    }else{
      if(!E(_r6/* seBB */.a)){
        return false;
      }else{
        _r5/* seBA */ = _r6/* seBB */.b;
        continue;
      }
    }
  }
},
_r7/* go1 */ = function(_r8/*  seBR */){
  while(1){
    var _r9/*  go1 */ = B((function(_ra/* seBR */){
      var _rb/* seBS */ = E(_ra/* seBR */);
      if(!_rb/* seBS */._){
        return __Z/* EXTERNAL */;
      }else{
        var _rc/* seBU */ = _rb/* seBS */.b,
        _rd/* seBV */ = E(_rb/* seBS */.a);
        switch(_rd/* seBV */._){
          case 0:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_re/* FormEngine.FormElement.Validation.validateElement2 */(_rd/* seBV */.b));
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 1:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_rd/* seBV */.b, _k/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 2:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_rd/* seBV */.b, _k/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 3:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_rd/* seBV */.b, _k/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 4:
            var _rf/* seD9 */ = _rd/* seBV */.a;
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rf/* seD9 */)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                var _rg/* seDq */ = E(_rd/* seBV */.b);
                if(!_rg/* seDq */._){
                  return false;
                }else{
                  if(E(_rg/* seDq */.a)<0){
                    return false;
                  }else{
                    var _rh/* seDw */ = E(_rf/* seD9 */);
                    if(_rh/* seDw */._==3){
                      if(E(_rh/* seDw */.b)._==1){
                        return B(_qT/* Data.Maybe.isJust */(_rd/* seBV */.c));
                      }else{
                        return true;
                      }
                    }else{
                      return E(_qV/* FormEngine.FormItem.nfiUnit1 */);
                    }
                  }
                }
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 5:
            var _ri/* seDE */ = _rd/* seBV */.a,
            _rj/* seDF */ = _rd/* seBV */.b;
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ri/* seDE */)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ri/* seDE */)).j)){
                  return B(_r4/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8G/* GHC.Base.map */(_rk/* FormEngine.FormElement.Validation.validateElement1 */, _rj/* seDF */))));
                }else{
                  if(!B(_qZ/* FormEngine.FormElement.Validation.validateElement_go */(_rj/* seDF */))){
                    return false;
                  }else{
                    return B(_r4/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8G/* GHC.Base.map */(_rk/* FormEngine.FormElement.Validation.validateElement1 */, _rj/* seDF */))));
                  }
                }
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 6:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_qT/* Data.Maybe.isJust */(_rd/* seBV */.b));
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 7:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_re/* FormEngine.FormElement.Validation.validateElement2 */(_rd/* seBV */.b));
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 8:
            return new T2(1,new T(function(){
              if(!E(_rd/* seBV */.b)){
                return true;
              }else{
                return B(_re/* FormEngine.FormElement.Validation.validateElement2 */(_rd/* seBV */.c));
              }
            }),new T(function(){
              return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
            }));
          case 9:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_re/* FormEngine.FormElement.Validation.validateElement2 */(_rd/* seBV */.b));
              }),new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          case 10:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8F/* GHC.Types.True */,new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
            break;
          default:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rd/* seBV */.a)).j)){
              _r8/*  seBR */ = _rc/* seBU */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8F/* GHC.Types.True */,new T(function(){
                return B(_r7/* FormEngine.FormElement.Validation.go1 */(_rc/* seBU */));
              }));
            }
        }
      }
    })(_r8/*  seBR */));
    if(_r9/*  go1 */!=__continue/* EXTERNAL */){
      return _r9/*  go1 */;
    }
  }
},
_re/* validateElement2 */ = function(_rl/* seFH */){
  return new F(function(){return _qW/* FormEngine.FormElement.Validation.go */(B(_r7/* FormEngine.FormElement.Validation.go1 */(_rl/* seFH */)));});
},
_rk/* validateElement1 */ = function(_rm/* seBK */){
  var _rn/* seBL */ = E(_rm/* seBK */);
  if(!_rn/* seBL */._){
    return true;
  }else{
    return new F(function(){return _re/* FormEngine.FormElement.Validation.validateElement2 */(_rn/* seBL */.c);});
  }
},
_ro/* validateElement */ = function(_rp/* seFJ */){
  var _rq/* seFK */ = E(_rp/* seFJ */);
  switch(_rq/* seFK */._){
    case 0:
      return new F(function(){return _re/* FormEngine.FormElement.Validation.validateElement2 */(_rq/* seFK */.b);});
      break;
    case 1:
      return (!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_rq/* seFK */.b, _k/* GHC.Types.[] */))) ? true : false;
    case 2:
      return (!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_rq/* seFK */.b, _k/* GHC.Types.[] */))) ? true : false;
    case 3:
      return (!B(_aD/* GHC.Classes.$fEq[]_$s$c==1 */(_rq/* seFK */.b, _k/* GHC.Types.[] */))) ? true : false;
    case 4:
      var _rr/* seG4 */ = E(_rq/* seFK */.b);
      if(!_rr/* seG4 */._){
        return false;
      }else{
        if(E(_rr/* seG4 */.a)<0){
          return false;
        }else{
          var _rs/* seGa */ = E(_rq/* seFK */.a);
          if(_rs/* seGa */._==3){
            if(E(_rs/* seGa */.b)._==1){
              return new F(function(){return _qT/* Data.Maybe.isJust */(_rq/* seFK */.c);});
            }else{
              return true;
            }
          }else{
            return E(_qV/* FormEngine.FormItem.nfiUnit1 */);
          }
        }
      }
      break;
    case 5:
      var _rt/* seGh */ = _rq/* seFK */.b;
      if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rq/* seFK */.a)).j)){
        return new F(function(){return _r4/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8G/* GHC.Base.map */(_rk/* FormEngine.FormElement.Validation.validateElement1 */, _rt/* seGh */)));});
      }else{
        if(!B(_qZ/* FormEngine.FormElement.Validation.validateElement_go */(_rt/* seGh */))){
          return false;
        }else{
          return new F(function(){return _r4/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8G/* GHC.Base.map */(_rk/* FormEngine.FormElement.Validation.validateElement1 */, _rt/* seGh */)));});
        }
      }
      break;
    case 6:
      return new F(function(){return _qT/* Data.Maybe.isJust */(_rq/* seFK */.b);});
      break;
    case 7:
      return new F(function(){return _re/* FormEngine.FormElement.Validation.validateElement2 */(_rq/* seFK */.b);});
      break;
    case 8:
      if(!E(_rq/* seFK */.b)){
        return true;
      }else{
        return new F(function(){return _re/* FormEngine.FormElement.Validation.validateElement2 */(_rq/* seFK */.c);});
      }
      break;
    case 9:
      return new F(function(){return _re/* FormEngine.FormElement.Validation.validateElement2 */(_rq/* seFK */.b);});
      break;
    case 10:
      return true;
    default:
      return true;
  }
},
_ru/* $wa */ = function(_rv/* sovk */, _rw/* sovl */, _rx/* sovm */, _/* EXTERNAL */){
  var _ry/* sovo */ = B(_nd/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_rv/* sovk */, _/* EXTERNAL */)),
  _rz/* sovs */ = B(_pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_ry/* sovo */, _rw/* sovl */, new T(function(){
    return B(_ro/* FormEngine.FormElement.Validation.validateElement */(_ry/* sovo */));
  },1), _/* EXTERNAL */)),
  _rA/* sovv */ = B(_qM/* FormEngine.FormElement.Updating.applyRules1 */(_rv/* sovk */, _rw/* sovl */, _/* EXTERNAL */)),
  _rB/* sovC */ = E(E(_rx/* sovm */).b);
  if(!_rB/* sovC */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_rB/* sovC */.a,_rv/* sovk */, _rw/* sovl */, _/* EXTERNAL */);});
  }
},
_rC/* $wa1 */ = function(_rD/* sovE */, _rE/* sovF */, _rF/* sovG */, _/* EXTERNAL */){
  var _rG/* sovI */ = B(_nd/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_rD/* sovE */, _/* EXTERNAL */)),
  _rH/* sovM */ = B(_pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_rG/* sovI */, _rE/* sovF */, new T(function(){
    return B(_ro/* FormEngine.FormElement.Validation.validateElement */(_rG/* sovI */));
  },1), _/* EXTERNAL */)),
  _rI/* sovP */ = B(_qM/* FormEngine.FormElement.Updating.applyRules1 */(_rD/* sovE */, _rE/* sovF */, _/* EXTERNAL */)),
  _rJ/* sovW */ = E(E(_rF/* sovG */).a);
  if(!_rJ/* sovW */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_rJ/* sovW */.a,_rD/* sovE */, _rE/* sovF */, _/* EXTERNAL */);});
  }
},
_rK/* $wa1 */ = function(_rL/* skfN */, _rM/* skfO */, _/* EXTERNAL */){
  var _rN/* skfT */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _rM/* skfO */),
  _rO/* skfZ */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _rN/* skfT */),
  _rP/* skga */ = eval/* EXTERNAL */(E(_o/* FormEngine.JQuery.addClass2 */)),
  _rQ/* skgi */ = __app2/* EXTERNAL */(E(_rP/* skga */), toJSStr/* EXTERNAL */(E(_rL/* skfN */)), _rO/* skfZ */);
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), _rQ/* skgi */);});
},
_rR/* $wa23 */ = function(_rS/* sk3k */, _rT/* sk3l */, _/* EXTERNAL */){
  var _rU/* sk3q */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _rT/* sk3l */),
  _rV/* sk3w */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _rU/* sk3q */),
  _rW/* sk3A */ = B(_1r/* FormEngine.JQuery.onClick1 */(_rS/* sk3k */, _rV/* sk3w */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_rW/* sk3A */));});
},
_rX/* onMouseEnter2 */ = "(function (ev, jq) { jq.mouseenter(ev); })",
_rY/* onMouseEnter1 */ = function(_rZ/* sjSI */, _s0/* sjSJ */, _/* EXTERNAL */){
  var _s1/* sjSV */ = __createJSFunc/* EXTERNAL */(2, function(_s2/* sjSM */, _/* EXTERNAL */){
    var _s3/* sjSO */ = B(A2(E(_rZ/* sjSI */),_s2/* sjSM */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _s4/* sjSY */ = E(_s0/* sjSJ */),
  _s5/* sjT3 */ = eval/* EXTERNAL */(E(_rX/* FormEngine.JQuery.onMouseEnter2 */)),
  _s6/* sjTb */ = __app2/* EXTERNAL */(E(_s5/* sjT3 */), _s1/* sjSV */, _s4/* sjSY */);
  return _s4/* sjSY */;
},
_s7/* $wa30 */ = function(_s8/* sk3R */, _s9/* sk3S */, _/* EXTERNAL */){
  var _sa/* sk3X */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _s9/* sk3S */),
  _sb/* sk43 */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _sa/* sk3X */),
  _sc/* sk47 */ = B(_rY/* FormEngine.JQuery.onMouseEnter1 */(_s8/* sk3R */, _sb/* sk43 */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_sc/* sk47 */));});
},
_sd/* onMouseLeave2 */ = "(function (ev, jq) { jq.mouseleave(ev); })",
_se/* onMouseLeave1 */ = function(_sf/* sjS9 */, _sg/* sjSa */, _/* EXTERNAL */){
  var _sh/* sjSm */ = __createJSFunc/* EXTERNAL */(2, function(_si/* sjSd */, _/* EXTERNAL */){
    var _sj/* sjSf */ = B(A2(E(_sf/* sjS9 */),_si/* sjSd */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _sk/* sjSp */ = E(_sg/* sjSa */),
  _sl/* sjSu */ = eval/* EXTERNAL */(E(_sd/* FormEngine.JQuery.onMouseLeave2 */)),
  _sm/* sjSC */ = __app2/* EXTERNAL */(E(_sl/* sjSu */), _sh/* sjSm */, _sk/* sjSp */);
  return _sk/* sjSp */;
},
_sn/* $wa31 */ = function(_so/* sk4o */, _sp/* sk4p */, _/* EXTERNAL */){
  var _sq/* sk4u */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _sp/* sk4p */),
  _sr/* sk4A */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _sq/* sk4u */),
  _ss/* sk4E */ = B(_se/* FormEngine.JQuery.onMouseLeave1 */(_so/* sk4o */, _sr/* sk4A */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_ss/* sk4E */));});
},
_st/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span class=\'short-desc\'>"));
}),
_su/* setTextInside1 */ = function(_sv/* sklS */, _sw/* sklT */, _/* EXTERNAL */){
  return new F(function(){return _12/* FormEngine.JQuery.$wa34 */(_sv/* sklS */, E(_sw/* sklT */), _/* EXTERNAL */);});
},
_sx/* a1 */ = function(_sy/* sour */, _sz/* sous */, _/* EXTERNAL */){
  var _sA/* souH */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_sy/* sour */)))).e);
  if(!_sA/* souH */._){
    return _sz/* sous */;
  }else{
    var _sB/* souL */ = B(_X/* FormEngine.JQuery.$wa3 */(_st/* FormEngine.FormElement.Rendering.lvl */, E(_sz/* sous */), _/* EXTERNAL */));
    return new F(function(){return _su/* FormEngine.JQuery.setTextInside1 */(_sA/* souH */.a, _sB/* souL */, _/* EXTERNAL */);});
  }
},
_sC/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label>"));
}),
_sD/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label class=\"link\" onclick=\""));
}),
_sE/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\">"));
}),
_sF/* a2 */ = function(_sG/* souO */, _sH/* souP */, _/* EXTERNAL */){
  var _sI/* souS */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_sG/* souO */)))),
  _sJ/* sov4 */ = E(_sI/* souS */.a);
  if(!_sJ/* sov4 */._){
    return _sH/* souP */;
  }else{
    var _sK/* sov5 */ = _sJ/* sov4 */.a,
    _sL/* sov6 */ = E(_sI/* souS */.i);
    if(!_sL/* sov6 */._){
      var _sM/* sov9 */ = B(_X/* FormEngine.JQuery.$wa3 */(_sC/* FormEngine.FormElement.Rendering.lvl1 */, E(_sH/* souP */), _/* EXTERNAL */));
      return new F(function(){return _su/* FormEngine.JQuery.setTextInside1 */(_sK/* sov5 */, _sM/* sov9 */, _/* EXTERNAL */);});
    }else{
      var _sN/* sovh */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_7/* GHC.Base.++ */(_sD/* FormEngine.FormElement.Rendering.lvl2 */, new T(function(){
        return B(_7/* GHC.Base.++ */(_sL/* sov6 */.a, _sE/* FormEngine.FormElement.Rendering.lvl3 */));
      },1))), E(_sH/* souP */), _/* EXTERNAL */));
      return new F(function(){return _su/* FormEngine.JQuery.setTextInside1 */(_sK/* sov5 */, _sN/* sovh */, _/* EXTERNAL */);});
    }
  }
},
_sO/* a3 */ = function(_sP/* sovY */, _/* EXTERNAL */){
  var _sQ/* sow2 */ = B(_2E/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_sP/* sovY */));
  }))), _/* EXTERNAL */)),
  _sR/* sow7 */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_sQ/* sow2 */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_sS/* setHtml2 */ = "(function (html, jq) { jq.html(html); return jq; })",
_sT/* $wa26 */ = function(_sU/* skjw */, _sV/* skjx */, _/* EXTERNAL */){
  var _sW/* skjH */ = eval/* EXTERNAL */(E(_sS/* FormEngine.JQuery.setHtml2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_sW/* skjH */), toJSStr/* EXTERNAL */(E(_sU/* skjw */)), _sV/* skjx */);});
},
_sX/* findSelector2 */ = "(function (elJs, jq) { return jq.find(elJs); })",
_sY/* $wa9 */ = function(_sZ/* skm0 */, _t0/* skm1 */, _/* EXTERNAL */){
  var _t1/* skmb */ = eval/* EXTERNAL */(E(_sX/* FormEngine.JQuery.findSelector2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_t1/* skmb */), toJSStr/* EXTERNAL */(E(_sZ/* skm0 */)), _t0/* skm1 */);});
},
_t2/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("span"));
}),
_t3/* a4 */ = function(_t4/* sowa */, _/* EXTERNAL */){
  var _t5/* sowe */ = B(_2E/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_t4/* sowa */));
  }))), _/* EXTERNAL */)),
  _t6/* sowh */ = E(_t5/* sowe */),
  _t7/* sowj */ = B(_sY/* FormEngine.JQuery.$wa9 */(_t2/* FormEngine.FormElement.Rendering.lvl4 */, _t6/* sowh */, _/* EXTERNAL */)),
  _t8/* sowz */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_t4/* sowa */)))).f);
  if(!_t8/* sowz */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _t9/* sowD */ = B(_sT/* FormEngine.JQuery.$wa26 */(_t8/* sowz */.a, E(_t7/* sowj */), _/* EXTERNAL */)),
    _ta/* sowG */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, _t6/* sowh */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_tb/* funcImg */ = function(_tc/* sefK */){
  return E(E(_tc/* sefK */).a);
},
_td/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd\'>"));
}),
_te/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_tf/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table>"));
}),
_tg/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tbody>"));
}),
_th/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tr>"));
}),
_ti/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td>"));
}),
_tj/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("more-space"));
}),
_tk/* $wa2 */ = function(_tl/* sowJ */, _tm/* sowK */, _tn/* sowL */, _to/* sowM */, _tp/* sowN */, _/* EXTERNAL */){
  var _tq/* sowP */ = B(_X/* FormEngine.JQuery.$wa3 */(_tf/* FormEngine.FormElement.Rendering.lvl5 */, _tp/* sowN */, _/* EXTERNAL */)),
  _tr/* sowX */ = B(_s7/* FormEngine.JQuery.$wa30 */(function(_ts/* sowU */, _/* EXTERNAL */){
    return new F(function(){return _t3/* FormEngine.FormElement.Rendering.a4 */(_tm/* sowK */, _/* EXTERNAL */);});
  }, E(_tq/* sowP */), _/* EXTERNAL */)),
  _tt/* sox5 */ = B(_sn/* FormEngine.JQuery.$wa31 */(function(_tu/* sox2 */, _/* EXTERNAL */){
    return new F(function(){return _sO/* FormEngine.FormElement.Rendering.a3 */(_tm/* sowK */, _/* EXTERNAL */);});
  }, E(_tr/* sowX */), _/* EXTERNAL */)),
  _tv/* soxa */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
  _tw/* soxd */ = __app1/* EXTERNAL */(_tv/* soxa */, E(_tt/* sox5 */)),
  _tx/* soxg */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
  _ty/* soxj */ = __app1/* EXTERNAL */(_tx/* soxg */, _tw/* soxd */),
  _tz/* soxm */ = B(_X/* FormEngine.JQuery.$wa3 */(_tg/* FormEngine.FormElement.Rendering.lvl6 */, _ty/* soxj */, _/* EXTERNAL */)),
  _tA/* soxs */ = __app1/* EXTERNAL */(_tv/* soxa */, E(_tz/* soxm */)),
  _tB/* soxw */ = __app1/* EXTERNAL */(_tx/* soxg */, _tA/* soxs */),
  _tC/* soxz */ = B(_X/* FormEngine.JQuery.$wa3 */(_th/* FormEngine.FormElement.Rendering.lvl7 */, _tB/* soxw */, _/* EXTERNAL */)),
  _tD/* soxF */ = __app1/* EXTERNAL */(_tv/* soxa */, E(_tC/* soxz */)),
  _tE/* soxJ */ = __app1/* EXTERNAL */(_tx/* soxg */, _tD/* soxF */),
  _tF/* soxQ */ = function(_/* EXTERNAL */, _tG/* soxS */){
    var _tH/* soxT */ = B(_X/* FormEngine.JQuery.$wa3 */(_td/* FormEngine.FormElement.Rendering.lvl10 */, _tG/* soxS */, _/* EXTERNAL */)),
    _tI/* soxZ */ = __app1/* EXTERNAL */(_tv/* soxa */, E(_tH/* soxT */)),
    _tJ/* soy3 */ = __app1/* EXTERNAL */(_tx/* soxg */, _tI/* soxZ */),
    _tK/* soy6 */ = B(_p/* FormEngine.JQuery.$wa */(_tj/* FormEngine.FormElement.Rendering.lvl9 */, _tJ/* soy3 */, _/* EXTERNAL */)),
    _tL/* soy9 */ = B(_sF/* FormEngine.FormElement.Rendering.a2 */(_tm/* sowK */, _tK/* soy6 */, _/* EXTERNAL */)),
    _tM/* soye */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
    _tN/* soyh */ = __app1/* EXTERNAL */(_tM/* soye */, E(_tL/* soy9 */)),
    _tO/* soyk */ = B(A1(_tl/* sowJ */,_/* EXTERNAL */)),
    _tP/* soyn */ = B(_X/* FormEngine.JQuery.$wa3 */(_ti/* FormEngine.FormElement.Rendering.lvl8 */, _tN/* soyh */, _/* EXTERNAL */)),
    _tQ/* soyt */ = __app1/* EXTERNAL */(_tv/* soxa */, E(_tP/* soyn */)),
    _tR/* soyx */ = __app1/* EXTERNAL */(_tx/* soxg */, _tQ/* soyt */),
    _tS/* soyF */ = __app2/* EXTERNAL */(E(_19/* FormEngine.JQuery.appendJq_f1 */), E(_tO/* soyk */), _tR/* soyx */),
    _tT/* soyJ */ = __app1/* EXTERNAL */(_tM/* soye */, _tS/* soyF */),
    _tU/* soyM */ = B(_X/* FormEngine.JQuery.$wa3 */(_ti/* FormEngine.FormElement.Rendering.lvl8 */, _tT/* soyJ */, _/* EXTERNAL */)),
    _tV/* soyS */ = B(_C/* FormEngine.JQuery.$wa20 */(_te/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
      return B(_pz/* FormEngine.FormElement.Identifiers.flagPlaceId */(_tm/* sowK */));
    },1), E(_tU/* soyM */), _/* EXTERNAL */)),
    _tW/* soyY */ = __app1/* EXTERNAL */(_tM/* soye */, E(_tV/* soyS */)),
    _tX/* soz2 */ = __app1/* EXTERNAL */(_tM/* soye */, _tW/* soyY */),
    _tY/* soz6 */ = __app1/* EXTERNAL */(_tM/* soye */, _tX/* soz2 */);
    return new F(function(){return _sx/* FormEngine.FormElement.Rendering.a1 */(_tm/* sowK */, _tY/* soz6 */, _/* EXTERNAL */);});
  },
  _tZ/* soza */ = E(E(_to/* sowM */).c);
  if(!_tZ/* soza */._){
    return new F(function(){return _tF/* soxQ */(_/* EXTERNAL */, _tE/* soxJ */);});
  }else{
    var _u0/* sozb */ = _tZ/* soza */.a,
    _u1/* sozc */ = B(_X/* FormEngine.JQuery.$wa3 */(_ti/* FormEngine.FormElement.Rendering.lvl8 */, _tE/* soxJ */, _/* EXTERNAL */)),
    _u2/* sozi */ = __app1/* EXTERNAL */(_tv/* soxa */, E(_u1/* sozc */)),
    _u3/* sozm */ = __app1/* EXTERNAL */(_tx/* soxg */, _u2/* sozi */),
    _u4/* sozp */ = B(_p/* FormEngine.JQuery.$wa */(_tj/* FormEngine.FormElement.Rendering.lvl9 */, _u3/* sozm */, _/* EXTERNAL */)),
    _u5/* sozv */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_tb/* FormEngine.Functionality.funcImg */(_u0/* sozb */)), E(_u4/* sozp */), _/* EXTERNAL */)),
    _u6/* sozA */ = new T(function(){
      return B(A2(E(_u0/* sozb */).b,_tm/* sowK */, _tn/* sowL */));
    }),
    _u7/* sozG */ = B(_rR/* FormEngine.JQuery.$wa23 */(function(_u8/* sozE */){
      return E(_u6/* sozA */);
    }, E(_u5/* sozv */), _/* EXTERNAL */)),
    _u9/* sozO */ = __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_u7/* sozG */));
    return new F(function(){return _tF/* soxQ */(_/* EXTERNAL */, _u9/* sozO */);});
  }
},
_ua/* a5 */ = function(_ub/* sozW */, _/* EXTERNAL */){
  while(1){
    var _uc/* sozY */ = E(_ub/* sozW */);
    if(!_uc/* sozY */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _ud/* soA3 */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_uc/* sozY */.a), _/* EXTERNAL */));
      _ub/* sozW */ = _uc/* sozY */.b;
      continue;
    }
  }
},
_ue/* appendT1 */ = function(_uf/* skeI */, _ug/* skeJ */, _/* EXTERNAL */){
  return new F(function(){return _X/* FormEngine.JQuery.$wa3 */(_uf/* skeI */, E(_ug/* skeJ */), _/* EXTERNAL */);});
},
_uh/* checkboxId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_optional_group"));
}),
_ui/* checkboxId */ = function(_uj/* sfrS */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_uj/* sfrS */)))).b)), _uh/* FormEngine.FormElement.Identifiers.checkboxId1 */);});
},
_uk/* errorjq1 */ = function(_ul/* sjY1 */, _um/* sjY2 */, _/* EXTERNAL */){
  var _un/* sjYc */ = eval/* EXTERNAL */(E(_2/* FormEngine.JQuery.errorIO2 */)),
  _uo/* sjYk */ = __app1/* EXTERNAL */(E(_un/* sjYc */), toJSStr/* EXTERNAL */(E(_ul/* sjY1 */)));
  return _um/* sjY2 */;
},
_up/* go */ = function(_uq/* sozR */, _ur/* sozS */){
  while(1){
    var _us/* sozT */ = E(_uq/* sozR */);
    if(!_us/* sozT */._){
      return E(_ur/* sozS */);
    }else{
      _uq/* sozR */ = _us/* sozT */.b;
      _ur/* sozS */ = _us/* sozT */.a;
      continue;
    }
  }
},
_ut/* isChecked_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.prop(\'checked\') === true; })");
}),
_uu/* isRadioSelected_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.length; })");
}),
_uv/* isRadioSelected1 */ = function(_uw/* skaN */, _/* EXTERNAL */){
  var _ux/* skaY */ = eval/* EXTERNAL */(E(_88/* FormEngine.JQuery.getRadioValue2 */)),
  _uy/* skb6 */ = __app1/* EXTERNAL */(E(_ux/* skaY */), toJSStr/* EXTERNAL */(B(_7/* GHC.Base.++ */(_8a/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_7/* GHC.Base.++ */(_uw/* skaN */, _89/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _uz/* skbc */ = __app1/* EXTERNAL */(E(_uu/* FormEngine.JQuery.isRadioSelected_f1 */), _uy/* skb6 */);
  return new T(function(){
    var _uA/* skbg */ = Number/* EXTERNAL */(_uz/* skbc */),
    _uB/* skbk */ = jsTrunc/* EXTERNAL */(_uA/* skbg */);
    return _uB/* skbk */>0;
  });
},
_uC/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_uD/* errorEmptyList */ = function(_uE/* s9sr */){
  return new F(function(){return err/* EXTERNAL */(B(_7/* GHC.Base.++ */(_5E/* GHC.List.prel_list_str */, new T(function(){
    return B(_7/* GHC.Base.++ */(_uE/* s9sr */, _uC/* GHC.List.lvl */));
  },1))));});
},
_uF/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_uG/* last1 */ = new T(function(){
  return B(_uD/* GHC.List.errorEmptyList */(_uF/* GHC.List.lvl16 */));
}),
_uH/* lfiAvailableOptions1 */ = new T(function(){
  return B(_oB/* Control.Exception.Base.recSelError */("lfiAvailableOptions"));
}),
_uI/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Submit"));
}),
_uJ/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("value"));
}),
_uK/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'button\' class=\'submit\'>"));
}),
_uL/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd more-space\' style=\'text-align: center\'>"));
}),
_uM/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table style=\'margin-top: 10px\'>"));
}),
_uN/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save"));
}),
_uO/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'submit\'>"));
}),
_uP/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElement rendering not implemented yet"));
}),
_uQ/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-section\'>"));
}),
_uR/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u25be"));
}),
_uS/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_uT/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("checked"));
}),
_uU/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("name"));
}),
_uV/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'checkbox\'>"));
}),
_uW/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("level"));
}),
_uX/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-group\'>"));
}),
_uY/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(">"));
}),
_uZ/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h"));
}),
_v0/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("framed"));
}),
_v1/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'simple-group\'>"));
}),
_v2/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("selected"));
}),
_v3/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<option>"));
}),
_v4/* lvl34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("identity"));
}),
_v5/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<select>"));
}),
_v6/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div>"));
}),
_v7/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<br>"));
}),
_v8/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'radio\'>"));
}),
_v9/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div></div>"));
}),
_va/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;&nbsp;"));
}),
_vb/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;"));
}),
_vc/* lvl42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'number\'>"));
}),
_vd/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'email\'>"));
}),
_ve/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<textarea>"));
}),
_vf/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'text\'>"));
}),
_vg/* lvl46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("renderElement did not unify"));
}),
_vh/* lvl47 */ = new T(function(){
  return B(_1M/* GHC.Show.$wshowSignedInt */(0, 0, _k/* GHC.Types.[] */));
}),
_vi/* onBlur2 */ = "(function (ev, jq) { jq.blur(ev); })",
_vj/* onBlur1 */ = function(_vk/* sjUY */, _vl/* sjUZ */, _/* EXTERNAL */){
  var _vm/* sjVb */ = __createJSFunc/* EXTERNAL */(2, function(_vn/* sjV2 */, _/* EXTERNAL */){
    var _vo/* sjV4 */ = B(A2(E(_vk/* sjUY */),_vn/* sjV2 */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _vp/* sjVe */ = E(_vl/* sjUZ */),
  _vq/* sjVj */ = eval/* EXTERNAL */(E(_vi/* FormEngine.JQuery.onBlur2 */)),
  _vr/* sjVr */ = __app2/* EXTERNAL */(E(_vq/* sjVj */), _vm/* sjVb */, _vp/* sjVe */);
  return _vp/* sjVe */;
},
_vs/* onChange2 */ = "(function (ev, jq) { jq.change(ev); })",
_vt/* onChange1 */ = function(_vu/* sjTh */, _vv/* sjTi */, _/* EXTERNAL */){
  var _vw/* sjTu */ = __createJSFunc/* EXTERNAL */(2, function(_vx/* sjTl */, _/* EXTERNAL */){
    var _vy/* sjTn */ = B(A2(E(_vu/* sjTh */),_vx/* sjTl */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _vz/* sjTx */ = E(_vv/* sjTi */),
  _vA/* sjTC */ = eval/* EXTERNAL */(E(_vs/* FormEngine.JQuery.onChange2 */)),
  _vB/* sjTK */ = __app2/* EXTERNAL */(E(_vA/* sjTC */), _vw/* sjTu */, _vz/* sjTx */);
  return _vz/* sjTx */;
},
_vC/* onKeyup2 */ = "(function (ev, jq) { jq.keyup(ev); })",
_vD/* onKeyup1 */ = function(_vE/* sjUp */, _vF/* sjUq */, _/* EXTERNAL */){
  var _vG/* sjUC */ = __createJSFunc/* EXTERNAL */(2, function(_vH/* sjUt */, _/* EXTERNAL */){
    var _vI/* sjUv */ = B(A2(E(_vE/* sjUp */),_vH/* sjUt */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _vJ/* sjUF */ = E(_vF/* sjUq */),
  _vK/* sjUK */ = eval/* EXTERNAL */(E(_vC/* FormEngine.JQuery.onKeyup2 */)),
  _vL/* sjUS */ = __app2/* EXTERNAL */(E(_vK/* sjUK */), _vG/* sjUC */, _vJ/* sjUF */);
  return _vJ/* sjUF */;
},
_vM/* optionElemValue */ = function(_vN/* sbUx */){
  var _vO/* sbUy */ = E(_vN/* sbUx */);
  if(!_vO/* sbUy */._){
    var _vP/* sbUB */ = E(_vO/* sbUy */.a);
    return (_vP/* sbUB */._==0) ? E(_vP/* sbUB */.a) : E(_vP/* sbUB */.b);
  }else{
    var _vQ/* sbUJ */ = E(_vO/* sbUy */.a);
    return (_vQ/* sbUJ */._==0) ? E(_vQ/* sbUJ */.a) : E(_vQ/* sbUJ */.b);
  }
},
_vR/* optionSectionId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_detail"));
}),
_vS/* filter */ = function(_vT/*  s9DD */, _vU/*  s9DE */){
  while(1){
    var _vV/*  filter */ = B((function(_vW/* s9DD */, _vX/* s9DE */){
      var _vY/* s9DF */ = E(_vX/* s9DE */);
      if(!_vY/* s9DF */._){
        return __Z/* EXTERNAL */;
      }else{
        var _vZ/* s9DG */ = _vY/* s9DF */.a,
        _w0/* s9DH */ = _vY/* s9DF */.b;
        if(!B(A1(_vW/* s9DD */,_vZ/* s9DG */))){
          var _w1/*   s9DD */ = _vW/* s9DD */;
          _vT/*  s9DD */ = _w1/*   s9DD */;
          _vU/*  s9DE */ = _w0/* s9DH */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_vZ/* s9DG */,new T(function(){
            return B(_vS/* GHC.List.filter */(_vW/* s9DD */, _w0/* s9DH */));
          }));
        }
      }
    })(_vT/*  s9DD */, _vU/*  s9DE */));
    if(_vV/*  filter */!=__continue/* EXTERNAL */){
      return _vV/*  filter */;
    }
  }
},
_w2/* $wlvl */ = function(_w3/* sfs7 */){
  var _w4/* sfs8 */ = function(_w5/* sfs9 */){
    var _w6/* sfsa */ = function(_w7/* sfsb */){
      if(_w3/* sfs7 */<48){
        switch(E(_w3/* sfs7 */)){
          case 45:
            return true;
          case 95:
            return true;
          default:
            return false;
        }
      }else{
        if(_w3/* sfs7 */>57){
          switch(E(_w3/* sfs7 */)){
            case 45:
              return true;
            case 95:
              return true;
            default:
              return false;
          }
        }else{
          return true;
        }
      }
    };
    if(_w3/* sfs7 */<97){
      return new F(function(){return _w6/* sfsa */(_/* EXTERNAL */);});
    }else{
      if(_w3/* sfs7 */>122){
        return new F(function(){return _w6/* sfsa */(_/* EXTERNAL */);});
      }else{
        return true;
      }
    }
  };
  if(_w3/* sfs7 */<65){
    return new F(function(){return _w4/* sfs8 */(_/* EXTERNAL */);});
  }else{
    if(_w3/* sfs7 */>90){
      return new F(function(){return _w4/* sfs8 */(_/* EXTERNAL */);});
    }else{
      return true;
    }
  }
},
_w8/* radioId1 */ = function(_w9/* sfsq */){
  return new F(function(){return _w2/* FormEngine.FormElement.Identifiers.$wlvl */(E(_w9/* sfsq */));});
},
_wa/* radioId2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_wb/* radioId */ = function(_wc/* sfst */, _wd/* sfsu */){
  var _we/* sft0 */ = new T(function(){
    return B(_7/* GHC.Base.++ */(_wa/* FormEngine.FormElement.Identifiers.radioId2 */, new T(function(){
      var _wf/* sfsJ */ = E(_wd/* sfsu */);
      if(!_wf/* sfsJ */._){
        var _wg/* sfsM */ = E(_wf/* sfsJ */.a);
        if(!_wg/* sfsM */._){
          return B(_vS/* GHC.List.filter */(_w8/* FormEngine.FormElement.Identifiers.radioId1 */, _wg/* sfsM */.a));
        }else{
          return B(_vS/* GHC.List.filter */(_w8/* FormEngine.FormElement.Identifiers.radioId1 */, _wg/* sfsM */.b));
        }
      }else{
        var _wh/* sfsU */ = E(_wf/* sfsJ */.a);
        if(!_wh/* sfsU */._){
          return B(_vS/* GHC.List.filter */(_w8/* FormEngine.FormElement.Identifiers.radioId1 */, _wh/* sfsU */.a));
        }else{
          return B(_vS/* GHC.List.filter */(_w8/* FormEngine.FormElement.Identifiers.radioId1 */, _wh/* sfsU */.b));
        }
      }
    },1)));
  },1);
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_wc/* sfst */)))).b)), _we/* sft0 */);});
},
_wi/* target_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (js) {return $(js.target); })");
}),
_wj/* foldElements2 */ = function(_wk/* soA6 */, _wl/* soA7 */, _wm/* soA8 */, _wn/* soA9 */, _/* EXTERNAL */){
  var _wo/* soAb */ = function(_wp/* soAc */, _/* EXTERNAL */){
    return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wk/* soA6 */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
  },
  _wq/* soAe */ = E(_wk/* soA6 */);
  switch(_wq/* soAe */._){
    case 0:
      return new F(function(){return _uk/* FormEngine.JQuery.errorjq1 */(_vg/* FormEngine.FormElement.Rendering.lvl46 */, _wn/* soA9 */, _/* EXTERNAL */);});
      break;
    case 1:
      var _wr/* soBq */ = function(_/* EXTERNAL */){
        var _ws/* soAo */ = B(_2E/* FormEngine.JQuery.select1 */(_vf/* FormEngine.FormElement.Rendering.lvl45 */, _/* EXTERNAL */)),
        _wt/* soAr */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_wq/* soAe */.a)),
        _wu/* soAG */ = B(_u/* FormEngine.JQuery.$wa6 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_wt/* soAr */.b)), E(_ws/* soAo */), _/* EXTERNAL */)),
        _wv/* soAJ */ = function(_/* EXTERNAL */, _ww/* soAL */){
          var _wx/* soAM */ = B(_u/* FormEngine.JQuery.$wa6 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _wq/* soAe */.b, _ww/* soAL */, _/* EXTERNAL */)),
          _wy/* soAS */ = B(_rY/* FormEngine.JQuery.onMouseEnter1 */(function(_wz/* soAP */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wx/* soAM */, _/* EXTERNAL */)),
          _wA/* soAY */ = B(_vD/* FormEngine.JQuery.onKeyup1 */(function(_wB/* soAV */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wy/* soAS */, _/* EXTERNAL */)),
          _wC/* soB4 */ = B(_vj/* FormEngine.JQuery.onBlur1 */(function(_wD/* soB1 */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wA/* soAY */, _/* EXTERNAL */));
          return new F(function(){return _se/* FormEngine.JQuery.onMouseLeave1 */(function(_wE/* soB7 */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wC/* soB4 */, _/* EXTERNAL */);});
        },
        _wF/* soBa */ = E(_wt/* soAr */.c);
        if(!_wF/* soBa */._){
          var _wG/* soBd */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_wu/* soAG */), _/* EXTERNAL */));
          return new F(function(){return _wv/* soAJ */(_/* EXTERNAL */, E(_wG/* soBd */));});
        }else{
          var _wH/* soBl */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _wF/* soBa */.a, E(_wu/* soAG */), _/* EXTERNAL */));
          return new F(function(){return _wv/* soAJ */(_/* EXTERNAL */, E(_wH/* soBl */));});
        }
      };
      return new F(function(){return _tk/* FormEngine.FormElement.Rendering.$wa2 */(_wr/* soBq */, _wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, E(_wn/* soA9 */), _/* EXTERNAL */);});
      break;
    case 2:
      var _wI/* soCz */ = function(_/* EXTERNAL */){
        var _wJ/* soBx */ = B(_2E/* FormEngine.JQuery.select1 */(_ve/* FormEngine.FormElement.Rendering.lvl44 */, _/* EXTERNAL */)),
        _wK/* soBA */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_wq/* soAe */.a)),
        _wL/* soBP */ = B(_u/* FormEngine.JQuery.$wa6 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_wK/* soBA */.b)), E(_wJ/* soBx */), _/* EXTERNAL */)),
        _wM/* soBS */ = function(_/* EXTERNAL */, _wN/* soBU */){
          var _wO/* soBV */ = B(_u/* FormEngine.JQuery.$wa6 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _wq/* soAe */.b, _wN/* soBU */, _/* EXTERNAL */)),
          _wP/* soC1 */ = B(_rY/* FormEngine.JQuery.onMouseEnter1 */(function(_wQ/* soBY */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wO/* soBV */, _/* EXTERNAL */)),
          _wR/* soC7 */ = B(_vD/* FormEngine.JQuery.onKeyup1 */(function(_wS/* soC4 */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wP/* soC1 */, _/* EXTERNAL */)),
          _wT/* soCd */ = B(_vj/* FormEngine.JQuery.onBlur1 */(function(_wU/* soCa */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wR/* soC7 */, _/* EXTERNAL */));
          return new F(function(){return _se/* FormEngine.JQuery.onMouseLeave1 */(function(_wV/* soCg */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _wT/* soCd */, _/* EXTERNAL */);});
        },
        _wW/* soCj */ = E(_wK/* soBA */.c);
        if(!_wW/* soCj */._){
          var _wX/* soCm */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_wL/* soBP */), _/* EXTERNAL */));
          return new F(function(){return _wM/* soBS */(_/* EXTERNAL */, E(_wX/* soCm */));});
        }else{
          var _wY/* soCu */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _wW/* soCj */.a, E(_wL/* soBP */), _/* EXTERNAL */));
          return new F(function(){return _wM/* soBS */(_/* EXTERNAL */, E(_wY/* soCu */));});
        }
      };
      return new F(function(){return _tk/* FormEngine.FormElement.Rendering.$wa2 */(_wI/* soCz */, _wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, E(_wn/* soA9 */), _/* EXTERNAL */);});
      break;
    case 3:
      var _wZ/* soDI */ = function(_/* EXTERNAL */){
        var _x0/* soCG */ = B(_2E/* FormEngine.JQuery.select1 */(_vd/* FormEngine.FormElement.Rendering.lvl43 */, _/* EXTERNAL */)),
        _x1/* soCJ */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_wq/* soAe */.a)),
        _x2/* soCY */ = B(_u/* FormEngine.JQuery.$wa6 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_x1/* soCJ */.b)), E(_x0/* soCG */), _/* EXTERNAL */)),
        _x3/* soD1 */ = function(_/* EXTERNAL */, _x4/* soD3 */){
          var _x5/* soD4 */ = B(_u/* FormEngine.JQuery.$wa6 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _wq/* soAe */.b, _x4/* soD3 */, _/* EXTERNAL */)),
          _x6/* soDa */ = B(_rY/* FormEngine.JQuery.onMouseEnter1 */(function(_x7/* soD7 */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _x5/* soD4 */, _/* EXTERNAL */)),
          _x8/* soDg */ = B(_vD/* FormEngine.JQuery.onKeyup1 */(function(_x9/* soDd */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _x6/* soDa */, _/* EXTERNAL */)),
          _xa/* soDm */ = B(_vj/* FormEngine.JQuery.onBlur1 */(function(_xb/* soDj */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _x8/* soDg */, _/* EXTERNAL */));
          return new F(function(){return _se/* FormEngine.JQuery.onMouseLeave1 */(function(_xc/* soDp */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _xa/* soDm */, _/* EXTERNAL */);});
        },
        _xd/* soDs */ = E(_x1/* soCJ */.c);
        if(!_xd/* soDs */._){
          var _xe/* soDv */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_x2/* soCY */), _/* EXTERNAL */));
          return new F(function(){return _x3/* soD1 */(_/* EXTERNAL */, E(_xe/* soDv */));});
        }else{
          var _xf/* soDD */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _xd/* soDs */.a, E(_x2/* soCY */), _/* EXTERNAL */));
          return new F(function(){return _x3/* soD1 */(_/* EXTERNAL */, E(_xf/* soDD */));});
        }
      };
      return new F(function(){return _tk/* FormEngine.FormElement.Rendering.$wa2 */(_wZ/* soDI */, _wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, E(_wn/* soA9 */), _/* EXTERNAL */);});
      break;
    case 4:
      var _xg/* soDJ */ = _wq/* soAe */.a,
      _xh/* soDP */ = function(_xi/* soDQ */, _/* EXTERNAL */){
        return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
      },
      _xj/* soJC */ = function(_/* EXTERNAL */){
        var _xk/* soDT */ = B(_2E/* FormEngine.JQuery.select1 */(_vc/* FormEngine.FormElement.Rendering.lvl42 */, _/* EXTERNAL */)),
        _xl/* soDW */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_xg/* soDJ */)),
        _xm/* soDY */ = _xl/* soDW */.b,
        _xn/* soEb */ = B(_u/* FormEngine.JQuery.$wa6 */(_te/* FormEngine.FormElement.Rendering.lvl11 */, B(_27/* FormEngine.FormItem.numbering2text */(_xm/* soDY */)), E(_xk/* soDT */), _/* EXTERNAL */)),
        _xo/* soEh */ = B(_u/* FormEngine.JQuery.$wa6 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_xm/* soDY */)), E(_xn/* soEb */), _/* EXTERNAL */)),
        _xp/* soEk */ = function(_/* EXTERNAL */, _xq/* soEm */){
          var _xr/* soEn */ = function(_/* EXTERNAL */, _xs/* soEp */){
            var _xt/* soEt */ = B(_rY/* FormEngine.JQuery.onMouseEnter1 */(function(_xu/* soEq */, _/* EXTERNAL */){
              return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
            }, _xs/* soEp */, _/* EXTERNAL */)),
            _xv/* soEz */ = B(_vD/* FormEngine.JQuery.onKeyup1 */(function(_xw/* soEw */, _/* EXTERNAL */){
              return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
            }, _xt/* soEt */, _/* EXTERNAL */)),
            _xx/* soEF */ = B(_vj/* FormEngine.JQuery.onBlur1 */(function(_xy/* soEC */, _/* EXTERNAL */){
              return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
            }, _xv/* soEz */, _/* EXTERNAL */)),
            _xz/* soEL */ = B(_se/* FormEngine.JQuery.onMouseLeave1 */(function(_xA/* soEI */, _/* EXTERNAL */){
              return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
            }, _xx/* soEF */, _/* EXTERNAL */)),
            _xB/* soEQ */ = B(_X/* FormEngine.JQuery.$wa3 */(_vb/* FormEngine.FormElement.Rendering.lvl41 */, E(_xz/* soEL */), _/* EXTERNAL */)),
            _xC/* soET */ = E(_xg/* soDJ */);
            if(_xC/* soET */._==3){
              var _xD/* soEX */ = E(_xC/* soET */.b);
              switch(_xD/* soEX */._){
                case 0:
                  return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_xD/* soEX */.a, _xB/* soEQ */, _/* EXTERNAL */);});
                  break;
                case 1:
                  var _xE/* soF0 */ = new T(function(){
                    return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(E(_xC/* soET */.a).b)), _8j/* FormEngine.FormItem.nfiUnitId1 */));
                  }),
                  _xF/* soFe */ = E(_xD/* soEX */.a);
                  if(!_xF/* soFe */._){
                    return _xB/* soEQ */;
                  }else{
                    var _xG/* soFf */ = _xF/* soFe */.a,
                    _xH/* soFg */ = _xF/* soFe */.b,
                    _xI/* soFj */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl38 */, E(_xB/* soEQ */), _/* EXTERNAL */)),
                    _xJ/* soFo */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _xG/* soFf */, E(_xI/* soFj */), _/* EXTERNAL */)),
                    _xK/* soFt */ = B(_C/* FormEngine.JQuery.$wa20 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, _xE/* soF0 */, E(_xJ/* soFo */), _/* EXTERNAL */)),
                    _xL/* soFy */ = B(_s7/* FormEngine.JQuery.$wa30 */(_wo/* soAb */, E(_xK/* soFt */), _/* EXTERNAL */)),
                    _xM/* soFD */ = B(_rR/* FormEngine.JQuery.$wa23 */(_wo/* soAb */, E(_xL/* soFy */), _/* EXTERNAL */)),
                    _xN/* soFI */ = B(_sn/* FormEngine.JQuery.$wa31 */(_xh/* soDP */, E(_xM/* soFD */), _/* EXTERNAL */)),
                    _xO/* soFL */ = function(_/* EXTERNAL */, _xP/* soFN */){
                      var _xQ/* soFO */ = B(_X/* FormEngine.JQuery.$wa3 */(_sC/* FormEngine.FormElement.Rendering.lvl1 */, _xP/* soFN */, _/* EXTERNAL */)),
                      _xR/* soFT */ = B(_12/* FormEngine.JQuery.$wa34 */(_xG/* soFf */, E(_xQ/* soFO */), _/* EXTERNAL */));
                      return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_va/* FormEngine.FormElement.Rendering.lvl40 */, _xR/* soFT */, _/* EXTERNAL */);});
                    },
                    _xS/* soFW */ = E(_wq/* soAe */.c);
                    if(!_xS/* soFW */._){
                      var _xT/* soFZ */ = B(_xO/* soFL */(_/* EXTERNAL */, E(_xN/* soFI */))),
                      _xU/* soG2 */ = function(_xV/* soG3 */, _xW/* soG4 */, _/* EXTERNAL */){
                        while(1){
                          var _xX/* soG6 */ = E(_xV/* soG3 */);
                          if(!_xX/* soG6 */._){
                            return _xW/* soG4 */;
                          }else{
                            var _xY/* soG7 */ = _xX/* soG6 */.a,
                            _xZ/* soGb */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl38 */, E(_xW/* soG4 */), _/* EXTERNAL */)),
                            _y0/* soGg */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _xY/* soG7 */, E(_xZ/* soGb */), _/* EXTERNAL */)),
                            _y1/* soGl */ = B(_C/* FormEngine.JQuery.$wa20 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, _xE/* soF0 */, E(_y0/* soGg */), _/* EXTERNAL */)),
                            _y2/* soGq */ = B(_s7/* FormEngine.JQuery.$wa30 */(_wo/* soAb */, E(_y1/* soGl */), _/* EXTERNAL */)),
                            _y3/* soGv */ = B(_rR/* FormEngine.JQuery.$wa23 */(_wo/* soAb */, E(_y2/* soGq */), _/* EXTERNAL */)),
                            _y4/* soGA */ = B(_sn/* FormEngine.JQuery.$wa31 */(_xh/* soDP */, E(_y3/* soGv */), _/* EXTERNAL */)),
                            _y5/* soGF */ = B(_X/* FormEngine.JQuery.$wa3 */(_sC/* FormEngine.FormElement.Rendering.lvl1 */, E(_y4/* soGA */), _/* EXTERNAL */)),
                            _y6/* soGK */ = B(_12/* FormEngine.JQuery.$wa34 */(_xY/* soG7 */, E(_y5/* soGF */), _/* EXTERNAL */)),
                            _y7/* soGP */ = B(_X/* FormEngine.JQuery.$wa3 */(_va/* FormEngine.FormElement.Rendering.lvl40 */, E(_y6/* soGK */), _/* EXTERNAL */));
                            _xV/* soG3 */ = _xX/* soG6 */.b;
                            _xW/* soG4 */ = _y7/* soGP */;
                            continue;
                          }
                        }
                      };
                      return new F(function(){return _xU/* soG2 */(_xH/* soFg */, _xT/* soFZ */, _/* EXTERNAL */);});
                    }else{
                      var _y8/* soGS */ = _xS/* soFW */.a;
                      if(!B(_2n/* GHC.Base.eqString */(_y8/* soGS */, _xG/* soFf */))){
                        var _y9/* soGW */ = B(_xO/* soFL */(_/* EXTERNAL */, E(_xN/* soFI */))),
                        _ya/* soGZ */ = function(_yb/*  soH0 */, _yc/*  soH1 */, _/* EXTERNAL */){
                          while(1){
                            var _yd/*  soGZ */ = B((function(_ye/* soH0 */, _yf/* soH1 */, _/* EXTERNAL */){
                              var _yg/* soH3 */ = E(_ye/* soH0 */);
                              if(!_yg/* soH3 */._){
                                return _yf/* soH1 */;
                              }else{
                                var _yh/* soH4 */ = _yg/* soH3 */.a,
                                _yi/* soH5 */ = _yg/* soH3 */.b,
                                _yj/* soH8 */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl38 */, E(_yf/* soH1 */), _/* EXTERNAL */)),
                                _yk/* soHd */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _yh/* soH4 */, E(_yj/* soH8 */), _/* EXTERNAL */)),
                                _yl/* soHi */ = B(_C/* FormEngine.JQuery.$wa20 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, _xE/* soF0 */, E(_yk/* soHd */), _/* EXTERNAL */)),
                                _ym/* soHn */ = B(_s7/* FormEngine.JQuery.$wa30 */(_wo/* soAb */, E(_yl/* soHi */), _/* EXTERNAL */)),
                                _yn/* soHs */ = B(_rR/* FormEngine.JQuery.$wa23 */(_wo/* soAb */, E(_ym/* soHn */), _/* EXTERNAL */)),
                                _yo/* soHx */ = B(_sn/* FormEngine.JQuery.$wa31 */(_xh/* soDP */, E(_yn/* soHs */), _/* EXTERNAL */)),
                                _yp/* soHA */ = function(_/* EXTERNAL */, _yq/* soHC */){
                                  var _yr/* soHD */ = B(_X/* FormEngine.JQuery.$wa3 */(_sC/* FormEngine.FormElement.Rendering.lvl1 */, _yq/* soHC */, _/* EXTERNAL */)),
                                  _ys/* soHI */ = B(_12/* FormEngine.JQuery.$wa34 */(_yh/* soH4 */, E(_yr/* soHD */), _/* EXTERNAL */));
                                  return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_va/* FormEngine.FormElement.Rendering.lvl40 */, _ys/* soHI */, _/* EXTERNAL */);});
                                };
                                if(!B(_2n/* GHC.Base.eqString */(_y8/* soGS */, _yh/* soH4 */))){
                                  var _yt/* soHO */ = B(_yp/* soHA */(_/* EXTERNAL */, E(_yo/* soHx */)));
                                  _yb/*  soH0 */ = _yi/* soH5 */;
                                  _yc/*  soH1 */ = _yt/* soHO */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _yu/* soHT */ = B(_C/* FormEngine.JQuery.$wa20 */(_uT/* FormEngine.FormElement.Rendering.lvl23 */, _uT/* FormEngine.FormElement.Rendering.lvl23 */, E(_yo/* soHx */), _/* EXTERNAL */)),
                                  _yv/* soHY */ = B(_yp/* soHA */(_/* EXTERNAL */, E(_yu/* soHT */)));
                                  _yb/*  soH0 */ = _yi/* soH5 */;
                                  _yc/*  soH1 */ = _yv/* soHY */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_yb/*  soH0 */, _yc/*  soH1 */, _/* EXTERNAL */));
                            if(_yd/*  soGZ */!=__continue/* EXTERNAL */){
                              return _yd/*  soGZ */;
                            }
                          }
                        };
                        return new F(function(){return _ya/* soGZ */(_xH/* soFg */, _y9/* soGW */, _/* EXTERNAL */);});
                      }else{
                        var _yw/* soI3 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uT/* FormEngine.FormElement.Rendering.lvl23 */, _uT/* FormEngine.FormElement.Rendering.lvl23 */, E(_xN/* soFI */), _/* EXTERNAL */)),
                        _yx/* soI8 */ = B(_xO/* soFL */(_/* EXTERNAL */, E(_yw/* soI3 */))),
                        _yy/* soIb */ = function(_yz/*  soIc */, _yA/*  soId */, _/* EXTERNAL */){
                          while(1){
                            var _yB/*  soIb */ = B((function(_yC/* soIc */, _yD/* soId */, _/* EXTERNAL */){
                              var _yE/* soIf */ = E(_yC/* soIc */);
                              if(!_yE/* soIf */._){
                                return _yD/* soId */;
                              }else{
                                var _yF/* soIg */ = _yE/* soIf */.a,
                                _yG/* soIh */ = _yE/* soIf */.b,
                                _yH/* soIk */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl38 */, E(_yD/* soId */), _/* EXTERNAL */)),
                                _yI/* soIp */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _yF/* soIg */, E(_yH/* soIk */), _/* EXTERNAL */)),
                                _yJ/* soIu */ = B(_C/* FormEngine.JQuery.$wa20 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, _xE/* soF0 */, E(_yI/* soIp */), _/* EXTERNAL */)),
                                _yK/* soIz */ = B(_s7/* FormEngine.JQuery.$wa30 */(_wo/* soAb */, E(_yJ/* soIu */), _/* EXTERNAL */)),
                                _yL/* soIE */ = B(_rR/* FormEngine.JQuery.$wa23 */(_wo/* soAb */, E(_yK/* soIz */), _/* EXTERNAL */)),
                                _yM/* soIJ */ = B(_sn/* FormEngine.JQuery.$wa31 */(_xh/* soDP */, E(_yL/* soIE */), _/* EXTERNAL */)),
                                _yN/* soIM */ = function(_/* EXTERNAL */, _yO/* soIO */){
                                  var _yP/* soIP */ = B(_X/* FormEngine.JQuery.$wa3 */(_sC/* FormEngine.FormElement.Rendering.lvl1 */, _yO/* soIO */, _/* EXTERNAL */)),
                                  _yQ/* soIU */ = B(_12/* FormEngine.JQuery.$wa34 */(_yF/* soIg */, E(_yP/* soIP */), _/* EXTERNAL */));
                                  return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_va/* FormEngine.FormElement.Rendering.lvl40 */, _yQ/* soIU */, _/* EXTERNAL */);});
                                };
                                if(!B(_2n/* GHC.Base.eqString */(_y8/* soGS */, _yF/* soIg */))){
                                  var _yR/* soJ0 */ = B(_yN/* soIM */(_/* EXTERNAL */, E(_yM/* soIJ */)));
                                  _yz/*  soIc */ = _yG/* soIh */;
                                  _yA/*  soId */ = _yR/* soJ0 */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _yS/* soJ5 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uT/* FormEngine.FormElement.Rendering.lvl23 */, _uT/* FormEngine.FormElement.Rendering.lvl23 */, E(_yM/* soIJ */), _/* EXTERNAL */)),
                                  _yT/* soJa */ = B(_yN/* soIM */(_/* EXTERNAL */, E(_yS/* soJ5 */)));
                                  _yz/*  soIc */ = _yG/* soIh */;
                                  _yA/*  soId */ = _yT/* soJa */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_yz/*  soIc */, _yA/*  soId */, _/* EXTERNAL */));
                            if(_yB/*  soIb */!=__continue/* EXTERNAL */){
                              return _yB/*  soIb */;
                            }
                          }
                        };
                        return new F(function(){return _yy/* soIb */(_xH/* soFg */, _yx/* soI8 */, _/* EXTERNAL */);});
                      }
                    }
                  }
                  break;
                default:
                  return _xB/* soEQ */;
              }
            }else{
              return E(_qV/* FormEngine.FormItem.nfiUnit1 */);
            }
          },
          _yU/* soJd */ = E(_wq/* soAe */.b);
          if(!_yU/* soJd */._){
            var _yV/* soJe */ = B(_u/* FormEngine.JQuery.$wa6 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _k/* GHC.Types.[] */, _xq/* soEm */, _/* EXTERNAL */));
            return new F(function(){return _xr/* soEn */(_/* EXTERNAL */, _yV/* soJe */);});
          }else{
            var _yW/* soJj */ = B(_u/* FormEngine.JQuery.$wa6 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, B(_1R/* GHC.Show.$fShowInt_$cshow */(_yU/* soJd */.a)), _xq/* soEm */, _/* EXTERNAL */));
            return new F(function(){return _xr/* soEn */(_/* EXTERNAL */, _yW/* soJj */);});
          }
        },
        _yX/* soJm */ = E(_xl/* soDW */.c);
        if(!_yX/* soJm */._){
          var _yY/* soJp */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_xo/* soEh */), _/* EXTERNAL */));
          return new F(function(){return _xp/* soEk */(_/* EXTERNAL */, E(_yY/* soJp */));});
        }else{
          var _yZ/* soJx */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _yX/* soJm */.a, E(_xo/* soEh */), _/* EXTERNAL */));
          return new F(function(){return _xp/* soEk */(_/* EXTERNAL */, E(_yZ/* soJx */));});
        }
      };
      return new F(function(){return _tk/* FormEngine.FormElement.Rendering.$wa2 */(_xj/* soJC */, _wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, E(_wn/* soA9 */), _/* EXTERNAL */);});
      break;
    case 5:
      var _z0/* soJD */ = _wq/* soAe */.a,
      _z1/* soJE */ = _wq/* soAe */.b,
      _z2/* soJG */ = new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_z0/* soJD */)).b));
      }),
      _z3/* soJV */ = new T(function(){
        var _z4/* soK8 */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_z0/* soJD */)).c);
        if(!_z4/* soK8 */._){
          return __Z/* EXTERNAL */;
        }else{
          return E(_z4/* soK8 */.a);
        }
      }),
      _z5/* soKa */ = function(_z6/* soKb */, _/* EXTERNAL */){
        var _z7/* soKd */ = B(_uv/* FormEngine.JQuery.isRadioSelected1 */(_z2/* soJG */, _/* EXTERNAL */));
        return new F(function(){return _pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_wq/* soAe */, _wl/* soA7 */, _z7/* soKd */, _/* EXTERNAL */);});
      },
      _z8/* soKg */ = new T(function(){
        return B(_up/* FormEngine.FormElement.Rendering.go */(_z1/* soJE */, _uG/* GHC.List.last1 */));
      }),
      _z9/* soKh */ = function(_za/* soKi */, _/* EXTERNAL */){
        return new F(function(){return _2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_uS/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
          return B(_7/* GHC.Base.++ */(B(_wb/* FormEngine.FormElement.Identifiers.radioId */(_wq/* soAe */, _za/* soKi */)), _vR/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
        },1))), _/* EXTERNAL */);});
      },
      _zb/* soKn */ = function(_zc/* soKo */, _/* EXTERNAL */){
        while(1){
          var _zd/* soKq */ = E(_zc/* soKo */);
          if(!_zd/* soKq */._){
            return _k/* GHC.Types.[] */;
          }else{
            var _ze/* soKs */ = _zd/* soKq */.b,
            _zf/* soKt */ = E(_zd/* soKq */.a);
            if(!_zf/* soKt */._){
              _zc/* soKo */ = _ze/* soKs */;
              continue;
            }else{
              var _zg/* soKz */ = B(_z9/* soKh */(_zf/* soKt */, _/* EXTERNAL */)),
              _zh/* soKC */ = B(_zb/* soKn */(_ze/* soKs */, _/* EXTERNAL */));
              return new T2(1,_zg/* soKz */,_zh/* soKC */);
            }
          }
        }
      },
      _zi/* soNf */ = function(_/* EXTERNAL */){
        var _zj/* soKH */ = B(_2E/* FormEngine.JQuery.select1 */(_v9/* FormEngine.FormElement.Rendering.lvl39 */, _/* EXTERNAL */)),
        _zk/* soKK */ = function(_zl/*  soKL */, _zm/*  soKM */, _/* EXTERNAL */){
          while(1){
            var _zn/*  soKK */ = B((function(_zo/* soKL */, _zp/* soKM */, _/* EXTERNAL */){
              var _zq/* soKO */ = E(_zo/* soKL */);
              if(!_zq/* soKO */._){
                return _zp/* soKM */;
              }else{
                var _zr/* soKP */ = _zq/* soKO */.a,
                _zs/* soKQ */ = _zq/* soKO */.b,
                _zt/* soKT */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl38 */, E(_zp/* soKM */), _/* EXTERNAL */)),
                _zu/* soKZ */ = B(_C/* FormEngine.JQuery.$wa20 */(_te/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_wb/* FormEngine.FormElement.Identifiers.radioId */(_wq/* soAe */, _zr/* soKP */));
                },1), E(_zt/* soKT */), _/* EXTERNAL */)),
                _zv/* soL4 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, _z2/* soJG */, E(_zu/* soKZ */), _/* EXTERNAL */)),
                _zw/* soL9 */ = B(_C/* FormEngine.JQuery.$wa20 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _z3/* soJV */, E(_zv/* soL4 */), _/* EXTERNAL */)),
                _zx/* soLf */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
                  return B(_vM/* FormEngine.FormElement.FormElement.optionElemValue */(_zr/* soKP */));
                },1), E(_zw/* soL9 */), _/* EXTERNAL */)),
                _zy/* soLi */ = function(_/* EXTERNAL */, _zz/* soLk */){
                  var _zA/* soLO */ = B(_rR/* FormEngine.JQuery.$wa23 */(function(_zB/* soLl */, _/* EXTERNAL */){
                    var _zC/* soLn */ = B(_zb/* soKn */(_z1/* soJE */, _/* EXTERNAL */)),
                    _zD/* soLq */ = B(_ua/* FormEngine.FormElement.Rendering.a5 */(_zC/* soLn */, _/* EXTERNAL */)),
                    _zE/* soLt */ = E(_zr/* soKP */);
                    if(!_zE/* soLt */._){
                      var _zF/* soLw */ = B(_uv/* FormEngine.JQuery.isRadioSelected1 */(_z2/* soJG */, _/* EXTERNAL */));
                      return new F(function(){return _pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_wq/* soAe */, _wl/* soA7 */, _zF/* soLw */, _/* EXTERNAL */);});
                    }else{
                      var _zG/* soLC */ = B(_z9/* soKh */(_zE/* soLt */, _/* EXTERNAL */)),
                      _zH/* soLH */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, E(_zG/* soLC */), _/* EXTERNAL */)),
                      _zI/* soLK */ = B(_uv/* FormEngine.JQuery.isRadioSelected1 */(_z2/* soJG */, _/* EXTERNAL */));
                      return new F(function(){return _pI/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_wq/* soAe */, _wl/* soA7 */, _zI/* soLK */, _/* EXTERNAL */);});
                    }
                  }, _zz/* soLk */, _/* EXTERNAL */)),
                  _zJ/* soLT */ = B(_sn/* FormEngine.JQuery.$wa31 */(_z5/* soKa */, E(_zA/* soLO */), _/* EXTERNAL */)),
                  _zK/* soLY */ = B(_X/* FormEngine.JQuery.$wa3 */(_sC/* FormEngine.FormElement.Rendering.lvl1 */, E(_zJ/* soLT */), _/* EXTERNAL */)),
                  _zL/* soM4 */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
                    return B(_vM/* FormEngine.FormElement.FormElement.optionElemValue */(_zr/* soKP */));
                  },1), E(_zK/* soLY */), _/* EXTERNAL */)),
                  _zM/* soM7 */ = E(_zr/* soKP */);
                  if(!_zM/* soM7 */._){
                    var _zN/* soM8 */ = _zM/* soM7 */.a,
                    _zO/* soMc */ = B(_X/* FormEngine.JQuery.$wa3 */(_k/* GHC.Types.[] */, E(_zL/* soM4 */), _/* EXTERNAL */)),
                    _zP/* soMf */ = E(_z8/* soKg */);
                    if(!_zP/* soMf */._){
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_zN/* soM8 */, _zP/* soMf */.a))){
                        return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_v7/* FormEngine.FormElement.Rendering.lvl37 */, _zO/* soMc */, _/* EXTERNAL */);});
                      }else{
                        return _zO/* soMc */;
                      }
                    }else{
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_zN/* soM8 */, _zP/* soMf */.a))){
                        return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_v7/* FormEngine.FormElement.Rendering.lvl37 */, _zO/* soMc */, _/* EXTERNAL */);});
                      }else{
                        return _zO/* soMc */;
                      }
                    }
                  }else{
                    var _zQ/* soMn */ = _zM/* soM7 */.a,
                    _zR/* soMs */ = B(_X/* FormEngine.JQuery.$wa3 */(_uR/* FormEngine.FormElement.Rendering.lvl21 */, E(_zL/* soM4 */), _/* EXTERNAL */)),
                    _zS/* soMv */ = E(_z8/* soKg */);
                    if(!_zS/* soMv */._){
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_zQ/* soMn */, _zS/* soMv */.a))){
                        return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_v7/* FormEngine.FormElement.Rendering.lvl37 */, _zR/* soMs */, _/* EXTERNAL */);});
                      }else{
                        return _zR/* soMs */;
                      }
                    }else{
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_zQ/* soMn */, _zS/* soMv */.a))){
                        return new F(function(){return _ue/* FormEngine.JQuery.appendT1 */(_v7/* FormEngine.FormElement.Rendering.lvl37 */, _zR/* soMs */, _/* EXTERNAL */);});
                      }else{
                        return _zR/* soMs */;
                      }
                    }
                  }
                },
                _zT/* soMD */ = E(_zr/* soKP */);
                if(!_zT/* soMD */._){
                  if(!E(_zT/* soMD */.b)){
                    var _zU/* soMJ */ = B(_zy/* soLi */(_/* EXTERNAL */, E(_zx/* soLf */)));
                    _zl/*  soKL */ = _zs/* soKQ */;
                    _zm/*  soKM */ = _zU/* soMJ */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _zV/* soMO */ = B(_C/* FormEngine.JQuery.$wa20 */(_uT/* FormEngine.FormElement.Rendering.lvl23 */, _uT/* FormEngine.FormElement.Rendering.lvl23 */, E(_zx/* soLf */), _/* EXTERNAL */)),
                    _zW/* soMT */ = B(_zy/* soLi */(_/* EXTERNAL */, E(_zV/* soMO */)));
                    _zl/*  soKL */ = _zs/* soKQ */;
                    _zm/*  soKM */ = _zW/* soMT */;
                    return __continue/* EXTERNAL */;
                  }
                }else{
                  if(!E(_zT/* soMD */.b)){
                    var _zX/* soN2 */ = B(_zy/* soLi */(_/* EXTERNAL */, E(_zx/* soLf */)));
                    _zl/*  soKL */ = _zs/* soKQ */;
                    _zm/*  soKM */ = _zX/* soN2 */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _zY/* soN7 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uT/* FormEngine.FormElement.Rendering.lvl23 */, _uT/* FormEngine.FormElement.Rendering.lvl23 */, E(_zx/* soLf */), _/* EXTERNAL */)),
                    _zZ/* soNc */ = B(_zy/* soLi */(_/* EXTERNAL */, E(_zY/* soN7 */)));
                    _zl/*  soKL */ = _zs/* soKQ */;
                    _zm/*  soKM */ = _zZ/* soNc */;
                    return __continue/* EXTERNAL */;
                  }
                }
              }
            })(_zl/*  soKL */, _zm/*  soKM */, _/* EXTERNAL */));
            if(_zn/*  soKK */!=__continue/* EXTERNAL */){
              return _zn/*  soKK */;
            }
          }
        };
        return new F(function(){return _zk/* soKK */(_z1/* soJE */, _zj/* soKH */, _/* EXTERNAL */);});
      },
      _A0/* soNg */ = B(_tk/* FormEngine.FormElement.Rendering.$wa2 */(_zi/* soNf */, _wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, E(_wn/* soA9 */), _/* EXTERNAL */)),
      _A1/* soNj */ = function(_A2/* soNk */, _A3/* soNl */, _/* EXTERNAL */){
        while(1){
          var _A4/* soNn */ = E(_A2/* soNk */);
          if(!_A4/* soNn */._){
            return _A3/* soNl */;
          }else{
            var _A5/* soNq */ = B(_wj/* FormEngine.FormElement.Rendering.foldElements2 */(_A4/* soNn */.a, _wl/* soA7 */, _wm/* soA8 */, _A3/* soNl */, _/* EXTERNAL */));
            _A2/* soNk */ = _A4/* soNn */.b;
            _A3/* soNl */ = _A5/* soNq */;
            continue;
          }
        }
      },
      _A6/* soNt */ = function(_A7/*  soNu */, _A8/*  soNv */, _/* EXTERNAL */){
        while(1){
          var _A9/*  soNt */ = B((function(_Aa/* soNu */, _Ab/* soNv */, _/* EXTERNAL */){
            var _Ac/* soNx */ = E(_Aa/* soNu */);
            if(!_Ac/* soNx */._){
              return _Ab/* soNv */;
            }else{
              var _Ad/* soNz */ = _Ac/* soNx */.b,
              _Ae/* soNA */ = E(_Ac/* soNx */.a);
              if(!_Ae/* soNA */._){
                var _Af/*   soNv */ = _Ab/* soNv */;
                _A7/*  soNu */ = _Ad/* soNz */;
                _A8/*  soNv */ = _Af/*   soNv */;
                return __continue/* EXTERNAL */;
              }else{
                var _Ag/* soNI */ = B(_X/* FormEngine.JQuery.$wa3 */(_v6/* FormEngine.FormElement.Rendering.lvl36 */, E(_Ab/* soNv */), _/* EXTERNAL */)),
                _Ah/* soNP */ = B(_C/* FormEngine.JQuery.$wa20 */(_te/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_7/* GHC.Base.++ */(B(_wb/* FormEngine.FormElement.Identifiers.radioId */(_wq/* soAe */, _Ae/* soNA */)), _vR/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                },1), E(_Ag/* soNI */), _/* EXTERNAL */)),
                _Ai/* soNU */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
                _Aj/* soNX */ = __app1/* EXTERNAL */(_Ai/* soNU */, E(_Ah/* soNP */)),
                _Ak/* soO0 */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
                _Al/* soO3 */ = __app1/* EXTERNAL */(_Ak/* soO0 */, _Aj/* soNX */),
                _Am/* soO6 */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, _Al/* soO3 */, _/* EXTERNAL */)),
                _An/* soO9 */ = B(_A1/* soNj */(_Ae/* soNA */.c, _Am/* soO6 */, _/* EXTERNAL */)),
                _Ao/* soOe */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
                _Ap/* soOh */ = __app1/* EXTERNAL */(_Ao/* soOe */, E(_An/* soO9 */)),
                _Aq/* soOk */ = function(_Ar/*  soOl */, _As/*  soOm */, _At/*  snPj */, _/* EXTERNAL */){
                  while(1){
                    var _Au/*  soOk */ = B((function(_Av/* soOl */, _Aw/* soOm */, _Ax/* snPj */, _/* EXTERNAL */){
                      var _Ay/* soOo */ = E(_Av/* soOl */);
                      if(!_Ay/* soOo */._){
                        return _Aw/* soOm */;
                      }else{
                        var _Az/* soOr */ = _Ay/* soOo */.b,
                        _AA/* soOs */ = E(_Ay/* soOo */.a);
                        if(!_AA/* soOs */._){
                          var _AB/*   soOm */ = _Aw/* soOm */,
                          _AC/*   snPj */ = _/* EXTERNAL */;
                          _Ar/*  soOl */ = _Az/* soOr */;
                          _As/*  soOm */ = _AB/*   soOm */;
                          _At/*  snPj */ = _AC/*   snPj */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _AD/* soOy */ = B(_X/* FormEngine.JQuery.$wa3 */(_v6/* FormEngine.FormElement.Rendering.lvl36 */, _Aw/* soOm */, _/* EXTERNAL */)),
                          _AE/* soOF */ = B(_C/* FormEngine.JQuery.$wa20 */(_te/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                            return B(_7/* GHC.Base.++ */(B(_wb/* FormEngine.FormElement.Identifiers.radioId */(_wq/* soAe */, _AA/* soOs */)), _vR/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                          },1), E(_AD/* soOy */), _/* EXTERNAL */)),
                          _AF/* soOL */ = __app1/* EXTERNAL */(_Ai/* soNU */, E(_AE/* soOF */)),
                          _AG/* soOP */ = __app1/* EXTERNAL */(_Ak/* soO0 */, _AF/* soOL */),
                          _AH/* soOS */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, _AG/* soOP */, _/* EXTERNAL */)),
                          _AI/* soOV */ = B(_A1/* soNj */(_AA/* soOs */.c, _AH/* soOS */, _/* EXTERNAL */)),
                          _AJ/* soP1 */ = __app1/* EXTERNAL */(_Ao/* soOe */, E(_AI/* soOV */)),
                          _AC/*   snPj */ = _/* EXTERNAL */;
                          _Ar/*  soOl */ = _Az/* soOr */;
                          _As/*  soOm */ = _AJ/* soP1 */;
                          _At/*  snPj */ = _AC/*   snPj */;
                          return __continue/* EXTERNAL */;
                        }
                      }
                    })(_Ar/*  soOl */, _As/*  soOm */, _At/*  snPj */, _/* EXTERNAL */));
                    if(_Au/*  soOk */!=__continue/* EXTERNAL */){
                      return _Au/*  soOk */;
                    }
                  }
                };
                return new F(function(){return _Aq/* soOk */(_Ad/* soNz */, _Ap/* soOh */, _/* EXTERNAL */, _/* EXTERNAL */);});
              }
            }
          })(_A7/*  soNu */, _A8/*  soNv */, _/* EXTERNAL */));
          if(_A9/*  soNt */!=__continue/* EXTERNAL */){
            return _A9/*  soNt */;
          }
        }
      };
      return new F(function(){return _A6/* soNt */(_z1/* soJE */, _A0/* soNg */, _/* EXTERNAL */);});
      break;
    case 6:
      var _AK/* soP4 */ = _wq/* soAe */.a,
      _AL/* soRY */ = function(_/* EXTERNAL */){
        var _AM/* soPa */ = B(_2E/* FormEngine.JQuery.select1 */(_v5/* FormEngine.FormElement.Rendering.lvl35 */, _/* EXTERNAL */)),
        _AN/* soPd */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_AK/* soP4 */)),
        _AO/* soPs */ = B(_u/* FormEngine.JQuery.$wa6 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_AN/* soPd */.b)), E(_AM/* soPa */), _/* EXTERNAL */)),
        _AP/* soPv */ = function(_/* EXTERNAL */, _AQ/* soPx */){
          var _AR/* soPB */ = B(_vj/* FormEngine.JQuery.onBlur1 */(function(_AS/* soPy */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _AQ/* soPx */, _/* EXTERNAL */)),
          _AT/* soPH */ = B(_vt/* FormEngine.JQuery.onChange1 */(function(_AU/* soPE */, _/* EXTERNAL */){
            return new F(function(){return _rC/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _AR/* soPB */, _/* EXTERNAL */)),
          _AV/* soPN */ = B(_se/* FormEngine.JQuery.onMouseLeave1 */(function(_AW/* soPK */, _/* EXTERNAL */){
            return new F(function(){return _ru/* FormEngine.FormElement.Rendering.$wa */(_wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, _/* EXTERNAL */);});
          }, _AT/* soPH */, _/* EXTERNAL */)),
          _AX/* soPQ */ = E(_AK/* soP4 */);
          if(_AX/* soPQ */._==5){
            var _AY/* soPU */ = E(_AX/* soPQ */.b);
            if(!_AY/* soPU */._){
              return _AV/* soPN */;
            }else{
              var _AZ/* soPW */ = _AY/* soPU */.b,
              _B0/* soPX */ = E(_AY/* soPU */.a),
              _B1/* soPY */ = _B0/* soPX */.a,
              _B2/* soQ2 */ = B(_X/* FormEngine.JQuery.$wa3 */(_v3/* FormEngine.FormElement.Rendering.lvl33 */, E(_AV/* soPN */), _/* EXTERNAL */)),
              _B3/* soQ7 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _B1/* soPY */, E(_B2/* soQ2 */), _/* EXTERNAL */)),
              _B4/* soQc */ = B(_12/* FormEngine.JQuery.$wa34 */(_B0/* soPX */.b, E(_B3/* soQ7 */), _/* EXTERNAL */)),
              _B5/* soQf */ = E(_wq/* soAe */.b);
              if(!_B5/* soQf */._){
                var _B6/* soQg */ = function(_B7/* soQh */, _B8/* soQi */, _/* EXTERNAL */){
                  while(1){
                    var _B9/* soQk */ = E(_B7/* soQh */);
                    if(!_B9/* soQk */._){
                      return _B8/* soQi */;
                    }else{
                      var _Ba/* soQn */ = E(_B9/* soQk */.a),
                      _Bb/* soQs */ = B(_X/* FormEngine.JQuery.$wa3 */(_v3/* FormEngine.FormElement.Rendering.lvl33 */, E(_B8/* soQi */), _/* EXTERNAL */)),
                      _Bc/* soQx */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _Ba/* soQn */.a, E(_Bb/* soQs */), _/* EXTERNAL */)),
                      _Bd/* soQC */ = B(_12/* FormEngine.JQuery.$wa34 */(_Ba/* soQn */.b, E(_Bc/* soQx */), _/* EXTERNAL */));
                      _B7/* soQh */ = _B9/* soQk */.b;
                      _B8/* soQi */ = _Bd/* soQC */;
                      continue;
                    }
                  }
                };
                return new F(function(){return _B6/* soQg */(_AZ/* soPW */, _B4/* soQc */, _/* EXTERNAL */);});
              }else{
                var _Be/* soQF */ = _B5/* soQf */.a;
                if(!B(_2n/* GHC.Base.eqString */(_B1/* soPY */, _Be/* soQF */))){
                  var _Bf/* soQH */ = function(_Bg/* soQI */, _Bh/* soQJ */, _/* EXTERNAL */){
                    while(1){
                      var _Bi/* soQL */ = E(_Bg/* soQI */);
                      if(!_Bi/* soQL */._){
                        return _Bh/* soQJ */;
                      }else{
                        var _Bj/* soQN */ = _Bi/* soQL */.b,
                        _Bk/* soQO */ = E(_Bi/* soQL */.a),
                        _Bl/* soQP */ = _Bk/* soQO */.a,
                        _Bm/* soQT */ = B(_X/* FormEngine.JQuery.$wa3 */(_v3/* FormEngine.FormElement.Rendering.lvl33 */, E(_Bh/* soQJ */), _/* EXTERNAL */)),
                        _Bn/* soQY */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _Bl/* soQP */, E(_Bm/* soQT */), _/* EXTERNAL */)),
                        _Bo/* soR3 */ = B(_12/* FormEngine.JQuery.$wa34 */(_Bk/* soQO */.b, E(_Bn/* soQY */), _/* EXTERNAL */));
                        if(!B(_2n/* GHC.Base.eqString */(_Bl/* soQP */, _Be/* soQF */))){
                          _Bg/* soQI */ = _Bj/* soQN */;
                          _Bh/* soQJ */ = _Bo/* soR3 */;
                          continue;
                        }else{
                          var _Bp/* soR9 */ = B(_C/* FormEngine.JQuery.$wa20 */(_v2/* FormEngine.FormElement.Rendering.lvl32 */, _v2/* FormEngine.FormElement.Rendering.lvl32 */, E(_Bo/* soR3 */), _/* EXTERNAL */));
                          _Bg/* soQI */ = _Bj/* soQN */;
                          _Bh/* soQJ */ = _Bp/* soR9 */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _Bf/* soQH */(_AZ/* soPW */, _B4/* soQc */, _/* EXTERNAL */);});
                }else{
                  var _Bq/* soRe */ = B(_C/* FormEngine.JQuery.$wa20 */(_v2/* FormEngine.FormElement.Rendering.lvl32 */, _v2/* FormEngine.FormElement.Rendering.lvl32 */, E(_B4/* soQc */), _/* EXTERNAL */)),
                  _Br/* soRh */ = function(_Bs/* soRi */, _Bt/* soRj */, _/* EXTERNAL */){
                    while(1){
                      var _Bu/* soRl */ = E(_Bs/* soRi */);
                      if(!_Bu/* soRl */._){
                        return _Bt/* soRj */;
                      }else{
                        var _Bv/* soRn */ = _Bu/* soRl */.b,
                        _Bw/* soRo */ = E(_Bu/* soRl */.a),
                        _Bx/* soRp */ = _Bw/* soRo */.a,
                        _By/* soRt */ = B(_X/* FormEngine.JQuery.$wa3 */(_v3/* FormEngine.FormElement.Rendering.lvl33 */, E(_Bt/* soRj */), _/* EXTERNAL */)),
                        _Bz/* soRy */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, _Bx/* soRp */, E(_By/* soRt */), _/* EXTERNAL */)),
                        _BA/* soRD */ = B(_12/* FormEngine.JQuery.$wa34 */(_Bw/* soRo */.b, E(_Bz/* soRy */), _/* EXTERNAL */));
                        if(!B(_2n/* GHC.Base.eqString */(_Bx/* soRp */, _Be/* soQF */))){
                          _Bs/* soRi */ = _Bv/* soRn */;
                          _Bt/* soRj */ = _BA/* soRD */;
                          continue;
                        }else{
                          var _BB/* soRJ */ = B(_C/* FormEngine.JQuery.$wa20 */(_v2/* FormEngine.FormElement.Rendering.lvl32 */, _v2/* FormEngine.FormElement.Rendering.lvl32 */, E(_BA/* soRD */), _/* EXTERNAL */));
                          _Bs/* soRi */ = _Bv/* soRn */;
                          _Bt/* soRj */ = _BB/* soRJ */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _Br/* soRh */(_AZ/* soPW */, _Bq/* soRe */, _/* EXTERNAL */);});
                }
              }
            }
          }else{
            return E(_uH/* FormEngine.FormItem.lfiAvailableOptions1 */);
          }
        },
        _BC/* soRM */ = E(_AN/* soPd */.c);
        if(!_BC/* soRM */._){
          var _BD/* soRP */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_AO/* soPs */), _/* EXTERNAL */));
          return new F(function(){return _AP/* soPv */(_/* EXTERNAL */, _BD/* soRP */);});
        }else{
          var _BE/* soRV */ = B(_u/* FormEngine.JQuery.$wa6 */(_v4/* FormEngine.FormElement.Rendering.lvl34 */, _BC/* soRM */.a, E(_AO/* soPs */), _/* EXTERNAL */));
          return new F(function(){return _AP/* soPv */(_/* EXTERNAL */, _BE/* soRV */);});
        }
      };
      return new F(function(){return _tk/* FormEngine.FormElement.Rendering.$wa2 */(_AL/* soRY */, _wq/* soAe */, _wl/* soA7 */, _wm/* soA8 */, E(_wn/* soA9 */), _/* EXTERNAL */);});
      break;
    case 7:
      var _BF/* soRZ */ = _wq/* soAe */.a,
      _BG/* soS0 */ = _wq/* soAe */.b,
      _BH/* soS4 */ = B(_X/* FormEngine.JQuery.$wa3 */(_v1/* FormEngine.FormElement.Rendering.lvl31 */, E(_wn/* soA9 */), _/* EXTERNAL */)),
      _BI/* soS9 */ = new T(function(){
        var _BJ/* soSa */ = E(_BF/* soRZ */);
        switch(_BJ/* soSa */._){
          case 7:
            return E(_BJ/* soSa */.b);
            break;
          case 8:
            return E(_BJ/* soSa */.b);
            break;
          case 9:
            return E(_BJ/* soSa */.b);
            break;
          default:
            return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }
      }),
      _BK/* soSl */ = B(_C/* FormEngine.JQuery.$wa20 */(_uW/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        return B(_1R/* GHC.Show.$fShowInt_$cshow */(_BI/* soS9 */));
      },1), E(_BH/* soS4 */), _/* EXTERNAL */)),
      _BL/* soSo */ = E(_BI/* soS9 */),
      _BM/* soSq */ = function(_/* EXTERNAL */, _BN/* soSs */){
        var _BO/* soSw */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _BN/* soSs */),
        _BP/* soSC */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _BO/* soSw */),
        _BQ/* soSF */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_BF/* soRZ */)),
        _BR/* soSK */ = _BQ/* soSF */.e,
        _BS/* soSR */ = E(_BQ/* soSF */.a);
        if(!_BS/* soSR */._){
          var _BT/* soSS */ = function(_/* EXTERNAL */, _BU/* soSU */){
            var _BV/* soSV */ = function(_BW/* soSW */, _BX/* soSX */, _/* EXTERNAL */){
              while(1){
                var _BY/* soSZ */ = E(_BW/* soSW */);
                if(!_BY/* soSZ */._){
                  return _BX/* soSX */;
                }else{
                  var _BZ/* soT2 */ = B(_wj/* FormEngine.FormElement.Rendering.foldElements2 */(_BY/* soSZ */.a, _wl/* soA7 */, _wm/* soA8 */, _BX/* soSX */, _/* EXTERNAL */));
                  _BW/* soSW */ = _BY/* soSZ */.b;
                  _BX/* soSX */ = _BZ/* soT2 */;
                  continue;
                }
              }
            },
            _C0/* soT5 */ = B(_BV/* soSV */(_BG/* soS0 */, _BU/* soSU */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_C0/* soT5 */));});
          },
          _C1/* soTh */ = E(_BR/* soSK */);
          if(!_C1/* soTh */._){
            return new F(function(){return _BT/* soSS */(_/* EXTERNAL */, _BP/* soSC */);});
          }else{
            var _C2/* soTk */ = B(_X/* FormEngine.JQuery.$wa3 */(_st/* FormEngine.FormElement.Rendering.lvl */, _BP/* soSC */, _/* EXTERNAL */)),
            _C3/* soTp */ = B(_12/* FormEngine.JQuery.$wa34 */(_C1/* soTh */.a, E(_C2/* soTk */), _/* EXTERNAL */));
            return new F(function(){return _BT/* soSS */(_/* EXTERNAL */, _C3/* soTp */);});
          }
        }else{
          var _C4/* soTw */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_7/* GHC.Base.++ */(_uZ/* FormEngine.FormElement.Rendering.lvl29 */, new T(function(){
            return B(_7/* GHC.Base.++ */(B(_1M/* GHC.Show.$wshowSignedInt */(0, _BL/* soSo */, _k/* GHC.Types.[] */)), _uY/* FormEngine.FormElement.Rendering.lvl28 */));
          },1))), _BP/* soSC */, _/* EXTERNAL */)),
          _C5/* soTB */ = B(_12/* FormEngine.JQuery.$wa34 */(_BS/* soSR */.a, E(_C4/* soTw */), _/* EXTERNAL */)),
          _C6/* soTE */ = function(_/* EXTERNAL */, _C7/* soTG */){
            var _C8/* soTH */ = function(_C9/* soTI */, _Ca/* soTJ */, _/* EXTERNAL */){
              while(1){
                var _Cb/* soTL */ = E(_C9/* soTI */);
                if(!_Cb/* soTL */._){
                  return _Ca/* soTJ */;
                }else{
                  var _Cc/* soTO */ = B(_wj/* FormEngine.FormElement.Rendering.foldElements2 */(_Cb/* soTL */.a, _wl/* soA7 */, _wm/* soA8 */, _Ca/* soTJ */, _/* EXTERNAL */));
                  _C9/* soTI */ = _Cb/* soTL */.b;
                  _Ca/* soTJ */ = _Cc/* soTO */;
                  continue;
                }
              }
            },
            _Cd/* soTR */ = B(_C8/* soTH */(_BG/* soS0 */, _C7/* soTG */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_Cd/* soTR */));});
          },
          _Ce/* soU3 */ = E(_BR/* soSK */);
          if(!_Ce/* soU3 */._){
            return new F(function(){return _C6/* soTE */(_/* EXTERNAL */, _C5/* soTB */);});
          }else{
            var _Cf/* soU7 */ = B(_X/* FormEngine.JQuery.$wa3 */(_st/* FormEngine.FormElement.Rendering.lvl */, E(_C5/* soTB */), _/* EXTERNAL */)),
            _Cg/* soUc */ = B(_12/* FormEngine.JQuery.$wa34 */(_Ce/* soU3 */.a, E(_Cf/* soU7 */), _/* EXTERNAL */));
            return new F(function(){return _C6/* soTE */(_/* EXTERNAL */, _Cg/* soUc */);});
          }
        }
      };
      if(_BL/* soSo */<=1){
        return new F(function(){return _BM/* soSq */(_/* EXTERNAL */, E(_BK/* soSl */));});
      }else{
        var _Ch/* soUl */ = B(_rK/* FormEngine.JQuery.$wa1 */(_v0/* FormEngine.FormElement.Rendering.lvl30 */, E(_BK/* soSl */), _/* EXTERNAL */));
        return new F(function(){return _BM/* soSq */(_/* EXTERNAL */, E(_Ch/* soUl */));});
      }
      break;
    case 8:
      var _Ci/* soUq */ = _wq/* soAe */.a,
      _Cj/* soUs */ = _wq/* soAe */.c,
      _Ck/* soUw */ = B(_X/* FormEngine.JQuery.$wa3 */(_uX/* FormEngine.FormElement.Rendering.lvl27 */, E(_wn/* soA9 */), _/* EXTERNAL */)),
      _Cl/* soUS */ = B(_C/* FormEngine.JQuery.$wa20 */(_uW/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        var _Cm/* soUB */ = E(_Ci/* soUq */);
        switch(_Cm/* soUB */._){
          case 7:
            return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_Cm/* soUB */.b), _k/* GHC.Types.[] */));
            break;
          case 8:
            return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_Cm/* soUB */.b), _k/* GHC.Types.[] */));
            break;
          case 9:
            return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_Cm/* soUB */.b), _k/* GHC.Types.[] */));
            break;
          default:
            return E(_vh/* FormEngine.FormElement.Rendering.lvl47 */);
        }
      },1), E(_Ck/* soUw */), _/* EXTERNAL */)),
      _Cn/* soV0 */ = B(_s7/* FormEngine.JQuery.$wa30 */(function(_Co/* soUX */, _/* EXTERNAL */){
        return new F(function(){return _t3/* FormEngine.FormElement.Rendering.a4 */(_wq/* soAe */, _/* EXTERNAL */);});
      }, E(_Cl/* soUS */), _/* EXTERNAL */)),
      _Cp/* soV8 */ = B(_sn/* FormEngine.JQuery.$wa31 */(function(_Cq/* soV5 */, _/* EXTERNAL */){
        return new F(function(){return _sO/* FormEngine.FormElement.Rendering.a3 */(_wq/* soAe */, _/* EXTERNAL */);});
      }, E(_Cn/* soV0 */), _/* EXTERNAL */)),
      _Cr/* soVd */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _Cs/* soVg */ = __app1/* EXTERNAL */(_Cr/* soVd */, E(_Cp/* soV8 */)),
      _Ct/* soVj */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _Cu/* soVm */ = __app1/* EXTERNAL */(_Ct/* soVj */, _Cs/* soVg */),
      _Cv/* soVp */ = B(_X/* FormEngine.JQuery.$wa3 */(_uV/* FormEngine.FormElement.Rendering.lvl25 */, _Cu/* soVm */, _/* EXTERNAL */)),
      _Cw/* soVH */ = B(_C/* FormEngine.JQuery.$wa20 */(_uU/* FormEngine.FormElement.Rendering.lvl24 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_Ci/* soUq */)).b));
      },1), E(_Cv/* soVp */), _/* EXTERNAL */)),
      _Cx/* soVK */ = function(_/* EXTERNAL */, _Cy/* soVM */){
        var _Cz/* soVN */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_uS/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
            return B(_ui/* FormEngine.FormElement.Identifiers.checkboxId */(_wq/* soAe */));
          },1)));
        }),
        _CA/* soWk */ = B(_rR/* FormEngine.JQuery.$wa23 */(function(_CB/* soVP */, _/* EXTERNAL */){
          var _CC/* soVR */ = B(_2E/* FormEngine.JQuery.select1 */(_Cz/* soVN */, _/* EXTERNAL */)),
          _CD/* soVZ */ = __app1/* EXTERNAL */(E(_wi/* FormEngine.JQuery.target_f1 */), E(_CB/* soVP */)),
          _CE/* soW5 */ = __app1/* EXTERNAL */(E(_ut/* FormEngine.JQuery.isChecked_f1 */), _CD/* soVZ */);
          if(!_CE/* soW5 */){
            var _CF/* soWb */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_CC/* soVR */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _CG/* soWg */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, E(_CC/* soVR */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        }, _Cy/* soVM */, _/* EXTERNAL */)),
        _CH/* soWn */ = B(_sF/* FormEngine.FormElement.Rendering.a2 */(_wq/* soAe */, _CA/* soWk */, _/* EXTERNAL */)),
        _CI/* soWq */ = function(_/* EXTERNAL */, _CJ/* soWs */){
          var _CK/* soWF */ = function(_/* EXTERNAL */, _CL/* soWH */){
            var _CM/* soWI */ = E(_Cj/* soUs */);
            if(!_CM/* soWI */._){
              return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), _CL/* soWH */);});
            }else{
              var _CN/* soWS */ = B(_X/* FormEngine.JQuery.$wa3 */(_uQ/* FormEngine.FormElement.Rendering.lvl20 */, _CL/* soWH */, _/* EXTERNAL */)),
              _CO/* soWY */ = B(_C/* FormEngine.JQuery.$wa20 */(_te/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                return B(_ui/* FormEngine.FormElement.Identifiers.checkboxId */(_wq/* soAe */));
              },1), E(_CN/* soWS */), _/* EXTERNAL */)),
              _CP/* soX4 */ = __app1/* EXTERNAL */(_Cr/* soVd */, E(_CO/* soWY */)),
              _CQ/* soX8 */ = __app1/* EXTERNAL */(_Ct/* soVj */, _CP/* soX4 */),
              _CR/* soXc */ = function(_CS/* soXk */, _CT/* soXl */, _/* EXTERNAL */){
                while(1){
                  var _CU/* soXn */ = E(_CS/* soXk */);
                  if(!_CU/* soXn */._){
                    return _CT/* soXl */;
                  }else{
                    var _CV/* soXq */ = B(_wj/* FormEngine.FormElement.Rendering.foldElements2 */(_CU/* soXn */.a, _wl/* soA7 */, _wm/* soA8 */, _CT/* soXl */, _/* EXTERNAL */));
                    _CS/* soXk */ = _CU/* soXn */.b;
                    _CT/* soXl */ = _CV/* soXq */;
                    continue;
                  }
                }
              },
              _CW/* soXu */ = B((function(_CX/* soXd */, _CY/* soXe */, _CZ/* soXf */, _/* EXTERNAL */){
                var _D0/* soXh */ = B(_wj/* FormEngine.FormElement.Rendering.foldElements2 */(_CX/* soXd */, _wl/* soA7 */, _wm/* soA8 */, _CZ/* soXf */, _/* EXTERNAL */));
                return new F(function(){return _CR/* soXc */(_CY/* soXe */, _D0/* soXh */, _/* EXTERNAL */);});
              })(_CM/* soWI */.a, _CM/* soWI */.b, _CQ/* soX8 */, _/* EXTERNAL */)),
              _D1/* soXz */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
              _D2/* soXC */ = __app1/* EXTERNAL */(_D1/* soXz */, E(_CW/* soXu */));
              return new F(function(){return __app1/* EXTERNAL */(_D1/* soXz */, _D2/* soXC */);});
            }
          },
          _D3/* soXK */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_Ci/* soUq */)).e);
          if(!_D3/* soXK */._){
            return new F(function(){return _CK/* soWF */(_/* EXTERNAL */, _CJ/* soWs */);});
          }else{
            var _D4/* soXM */ = B(_X/* FormEngine.JQuery.$wa3 */(_st/* FormEngine.FormElement.Rendering.lvl */, _CJ/* soWs */, _/* EXTERNAL */)),
            _D5/* soXR */ = B(_12/* FormEngine.JQuery.$wa34 */(_D3/* soXK */.a, E(_D4/* soXM */), _/* EXTERNAL */));
            return new F(function(){return _CK/* soWF */(_/* EXTERNAL */, E(_D5/* soXR */));});
          }
        };
        if(!E(_Cj/* soUs */)._){
          var _D6/* soXZ */ = B(_X/* FormEngine.JQuery.$wa3 */(_k/* GHC.Types.[] */, E(_CH/* soWn */), _/* EXTERNAL */));
          return new F(function(){return _CI/* soWq */(_/* EXTERNAL */, E(_D6/* soXZ */));});
        }else{
          var _D7/* soY8 */ = B(_X/* FormEngine.JQuery.$wa3 */(_uR/* FormEngine.FormElement.Rendering.lvl21 */, E(_CH/* soWn */), _/* EXTERNAL */));
          return new F(function(){return _CI/* soWq */(_/* EXTERNAL */, E(_D7/* soY8 */));});
        }
      };
      if(!E(_wq/* soAe */.b)){
        return new F(function(){return _Cx/* soVK */(_/* EXTERNAL */, E(_Cw/* soVH */));});
      }else{
        var _D8/* soYi */ = B(_C/* FormEngine.JQuery.$wa20 */(_uT/* FormEngine.FormElement.Rendering.lvl23 */, _uT/* FormEngine.FormElement.Rendering.lvl23 */, E(_Cw/* soVH */), _/* EXTERNAL */));
        return new F(function(){return _Cx/* soVK */(_/* EXTERNAL */, E(_D8/* soYi */));});
      }
      break;
    case 9:
      return new F(function(){return _uk/* FormEngine.JQuery.errorjq1 */(_uP/* FormEngine.FormElement.Rendering.lvl19 */, _wn/* soA9 */, _/* EXTERNAL */);});
      break;
    case 10:
      var _D9/* soYu */ = B(_X/* FormEngine.JQuery.$wa3 */(_uM/* FormEngine.FormElement.Rendering.lvl16 */, E(_wn/* soA9 */), _/* EXTERNAL */)),
      _Da/* soYz */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _Db/* soYC */ = __app1/* EXTERNAL */(_Da/* soYz */, E(_D9/* soYu */)),
      _Dc/* soYF */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _Dd/* soYI */ = __app1/* EXTERNAL */(_Dc/* soYF */, _Db/* soYC */),
      _De/* soYL */ = B(_X/* FormEngine.JQuery.$wa3 */(_tg/* FormEngine.FormElement.Rendering.lvl6 */, _Dd/* soYI */, _/* EXTERNAL */)),
      _Df/* soYR */ = __app1/* EXTERNAL */(_Da/* soYz */, E(_De/* soYL */)),
      _Dg/* soYV */ = __app1/* EXTERNAL */(_Dc/* soYF */, _Df/* soYR */),
      _Dh/* soYY */ = B(_X/* FormEngine.JQuery.$wa3 */(_th/* FormEngine.FormElement.Rendering.lvl7 */, _Dg/* soYV */, _/* EXTERNAL */)),
      _Di/* soZ4 */ = __app1/* EXTERNAL */(_Da/* soYz */, E(_Dh/* soYY */)),
      _Dj/* soZ8 */ = __app1/* EXTERNAL */(_Dc/* soYF */, _Di/* soZ4 */),
      _Dk/* soZb */ = B(_X/* FormEngine.JQuery.$wa3 */(_uL/* FormEngine.FormElement.Rendering.lvl15 */, _Dj/* soZ8 */, _/* EXTERNAL */)),
      _Dl/* soZh */ = __app1/* EXTERNAL */(_Da/* soYz */, E(_Dk/* soZb */)),
      _Dm/* soZl */ = __app1/* EXTERNAL */(_Dc/* soYF */, _Dl/* soZh */),
      _Dn/* soZo */ = B(_X/* FormEngine.JQuery.$wa3 */(_uO/* FormEngine.FormElement.Rendering.lvl18 */, _Dm/* soZl */, _/* EXTERNAL */)),
      _Do/* soZI */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _Dp/* soZF */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_wq/* soAe */.a)).a);
        if(!_Dp/* soZF */._){
          return E(_uN/* FormEngine.FormElement.Rendering.lvl17 */);
        }else{
          return E(_Dp/* soZF */.a);
        }
      },1), E(_Dn/* soZo */), _/* EXTERNAL */)),
      _Dq/* soZN */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _Dr/* soZQ */ = __app1/* EXTERNAL */(_Dq/* soZN */, E(_Do/* soZI */)),
      _Ds/* soZU */ = __app1/* EXTERNAL */(_Dq/* soZN */, _Dr/* soZQ */),
      _Dt/* soZY */ = __app1/* EXTERNAL */(_Dq/* soZN */, _Ds/* soZU */),
      _Du/* sp02 */ = __app1/* EXTERNAL */(_Dq/* soZN */, _Dt/* soZY */);
      return new F(function(){return _sx/* FormEngine.FormElement.Rendering.a1 */(_wq/* soAe */, _Du/* sp02 */, _/* EXTERNAL */);});
      break;
    default:
      var _Dv/* sp0a */ = B(_X/* FormEngine.JQuery.$wa3 */(_uM/* FormEngine.FormElement.Rendering.lvl16 */, E(_wn/* soA9 */), _/* EXTERNAL */)),
      _Dw/* sp0f */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _Dx/* sp0i */ = __app1/* EXTERNAL */(_Dw/* sp0f */, E(_Dv/* sp0a */)),
      _Dy/* sp0l */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _Dz/* sp0o */ = __app1/* EXTERNAL */(_Dy/* sp0l */, _Dx/* sp0i */),
      _DA/* sp0r */ = B(_X/* FormEngine.JQuery.$wa3 */(_tg/* FormEngine.FormElement.Rendering.lvl6 */, _Dz/* sp0o */, _/* EXTERNAL */)),
      _DB/* sp0x */ = __app1/* EXTERNAL */(_Dw/* sp0f */, E(_DA/* sp0r */)),
      _DC/* sp0B */ = __app1/* EXTERNAL */(_Dy/* sp0l */, _DB/* sp0x */),
      _DD/* sp0E */ = B(_X/* FormEngine.JQuery.$wa3 */(_th/* FormEngine.FormElement.Rendering.lvl7 */, _DC/* sp0B */, _/* EXTERNAL */)),
      _DE/* sp0K */ = __app1/* EXTERNAL */(_Dw/* sp0f */, E(_DD/* sp0E */)),
      _DF/* sp0O */ = __app1/* EXTERNAL */(_Dy/* sp0l */, _DE/* sp0K */),
      _DG/* sp0R */ = B(_X/* FormEngine.JQuery.$wa3 */(_uL/* FormEngine.FormElement.Rendering.lvl15 */, _DF/* sp0O */, _/* EXTERNAL */)),
      _DH/* sp0X */ = __app1/* EXTERNAL */(_Dw/* sp0f */, E(_DG/* sp0R */)),
      _DI/* sp11 */ = __app1/* EXTERNAL */(_Dy/* sp0l */, _DH/* sp0X */),
      _DJ/* sp14 */ = B(_X/* FormEngine.JQuery.$wa3 */(_uK/* FormEngine.FormElement.Rendering.lvl14 */, _DI/* sp11 */, _/* EXTERNAL */)),
      _DK/* sp1o */ = B(_C/* FormEngine.JQuery.$wa20 */(_uJ/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _DL/* sp1l */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_wq/* soAe */.a)).a);
        if(!_DL/* sp1l */._){
          return E(_uI/* FormEngine.FormElement.Rendering.lvl12 */);
        }else{
          return E(_DL/* sp1l */.a);
        }
      },1), E(_DJ/* sp14 */), _/* EXTERNAL */)),
      _DM/* sp1t */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _DN/* sp1w */ = __app1/* EXTERNAL */(_DM/* sp1t */, E(_DK/* sp1o */)),
      _DO/* sp1A */ = __app1/* EXTERNAL */(_DM/* sp1t */, _DN/* sp1w */),
      _DP/* sp1E */ = __app1/* EXTERNAL */(_DM/* sp1t */, _DO/* sp1A */),
      _DQ/* sp1I */ = __app1/* EXTERNAL */(_DM/* sp1t */, _DP/* sp1E */);
      return new F(function(){return _sx/* FormEngine.FormElement.Rendering.a1 */(_wq/* soAe */, _DQ/* sp1I */, _/* EXTERNAL */);});
  }
},
_DR/* foldElements1 */ = function(_DS/* sp1M */, _DT/* sp1N */, _DU/* sp1O */, _DV/* sp1P */, _/* EXTERNAL */){
  var _DW/* sp1R */ = function(_DX/* sp1S */, _DY/* sp1T */, _/* EXTERNAL */){
    while(1){
      var _DZ/* sp1V */ = E(_DX/* sp1S */);
      if(!_DZ/* sp1V */._){
        return _DY/* sp1T */;
      }else{
        var _E0/* sp1Y */ = B(_wj/* FormEngine.FormElement.Rendering.foldElements2 */(_DZ/* sp1V */.a, _DT/* sp1N */, _DU/* sp1O */, _DY/* sp1T */, _/* EXTERNAL */));
        _DX/* sp1S */ = _DZ/* sp1V */.b;
        _DY/* sp1T */ = _E0/* sp1Y */;
        continue;
      }
    }
  };
  return new F(function(){return _DW/* sp1R */(_DS/* sp1M */, _DV/* sp1P */, _/* EXTERNAL */);});
},
_E1/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/invalid.png\'/>"));
}),
_E2/* baseURL */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/"));
}),
_E3/* staticURL1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("static/"));
}),
_E4/* staticURL */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_E2/* Config.Config.baseURL */, _E3/* Config.Config.staticURL1 */));
}),
_E5/* lvl11 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_E4/* Config.Config.staticURL */, _E1/* Form.lvl10 */));
}),
_E6/* lvl12 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'invalid\' class=\'validity-flag\' src=\'", _E5/* Form.lvl11 */));
}),
_E7/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/question.png\'/>"));
}),
_E8/* lvl14 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_E4/* Config.Config.staticURL */, _E7/* Form.lvl13 */));
}),
_E9/* lvl15 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'details\' src=\'", _E8/* Form.lvl14 */));
}),
_Ea/* Just */ = function(_Eb/* B1 */){
  return new T1(1,_Eb/* B1 */);
},
_Ec/* $fJSTypeJSString */ = new T2(0,_bL/* GHC.Base.id */,_Ea/* GHC.Base.Just */),
_Ed/* fromJSStr */ = function(_Ee/* sdrS */){
  return new F(function(){return fromJSStr/* EXTERNAL */(E(_Ee/* sdrS */));});
},
_Ef/* $fJSType[]_$cfromJSString */ = function(_Eg/* s3BE */){
  return new T1(1,new T(function(){
    return B(_Ed/* GHC.HastePrim.fromJSStr */(_Eg/* s3BE */));
  }));
},
_Eh/* toJSStr1 */ = function(_Ei/* sdrX */){
  return new F(function(){return toJSStr/* EXTERNAL */(E(_Ei/* sdrX */));});
},
_Ej/* $fJSType[] */ = new T2(0,_Eh/* GHC.HastePrim.toJSStr1 */,_Ef/* Haste.Prim.JSType.$fJSType[]_$cfromJSString */),
_Ek/* $fApplicativeIO1 */ = function(_El/* s3hg */, _Em/* s3hh */, _/* EXTERNAL */){
  var _En/* s3hj */ = B(A1(_El/* s3hg */,_/* EXTERNAL */)),
  _Eo/* s3hm */ = B(A1(_Em/* s3hh */,_/* EXTERNAL */));
  return _En/* s3hj */;
},
_Ep/* $fApplicativeIO2 */ = function(_Eq/* s3gu */, _Er/* s3gv */, _/* EXTERNAL */){
  var _Es/* s3gx */ = B(A1(_Eq/* s3gu */,_/* EXTERNAL */)),
  _Et/* s3gA */ = B(A1(_Er/* s3gv */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_Es/* s3gx */,_Et/* s3gA */));
  });
},
_Eu/* $fFunctorIO1 */ = function(_Ev/* s3gZ */, _Ew/* s3h0 */, _/* EXTERNAL */){
  var _Ex/* s3h2 */ = B(A1(_Ew/* s3h0 */,_/* EXTERNAL */));
  return _Ev/* s3gZ */;
},
_Ey/* $fFunctorIO2 */ = function(_Ez/* s3gS */, _EA/* s3gT */, _/* EXTERNAL */){
  var _EB/* s3gV */ = B(A1(_EA/* s3gT */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_Ez/* s3gS */,_EB/* s3gV */));
  });
},
_EC/* $fFunctorIO */ = new T2(0,_Ey/* GHC.Base.$fFunctorIO2 */,_Eu/* GHC.Base.$fFunctorIO1 */),
_ED/* returnIO1 */ = function(_EE/* s3g7 */, _/* EXTERNAL */){
  return _EE/* s3g7 */;
},
_EF/* thenIO1 */ = function(_EG/* s3g1 */, _EH/* s3g2 */, _/* EXTERNAL */){
  var _EI/* s3g4 */ = B(A1(_EG/* s3g1 */,_/* EXTERNAL */));
  return new F(function(){return A1(_EH/* s3g2 */,_/* EXTERNAL */);});
},
_EJ/* $fApplicativeIO */ = new T5(0,_EC/* GHC.Base.$fFunctorIO */,_ED/* GHC.Base.returnIO1 */,_Ep/* GHC.Base.$fApplicativeIO2 */,_EF/* GHC.Base.thenIO1 */,_Ek/* GHC.Base.$fApplicativeIO1 */),
_EK/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_EL/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_EM/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_EN/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_EK/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_EL/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_EM/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_EO/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_EN/* GHC.IO.Exception.$fExceptionIOException_wild */,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */),
_EP/* $fExceptionIOException3 */ = function(_EQ/* s3K6Q */){
  return E(_EO/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_ER/* $fExceptionIOException_$cfromException */ = function(_ES/* s3KaB */){
  var _ET/* s3KaC */ = E(_ES/* s3KaB */);
  return new F(function(){return _8T/* Data.Typeable.cast */(B(_8R/* GHC.Exception.$p1Exception */(_ET/* s3KaC */.a)), _EP/* GHC.IO.Exception.$fExceptionIOException3 */, _ET/* s3KaC */.b);});
},
_EU/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_EV/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_EW/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_EX/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_EY/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_EZ/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_F0/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_F1/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_F2/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_F3/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_F4/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_F5/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_F6/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_F7/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_F8/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_F9/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_Fa/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_Fb/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_Fc/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_Fd/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_Fe/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_Ff/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_Fg/* $w$cshowsPrec3 */ = function(_Fh/* s3Kcg */, _Fi/* s3Kch */){
  switch(E(_Fh/* s3Kcg */)){
    case 0:
      return new F(function(){return _7/* GHC.Base.++ */(_F7/* GHC.IO.Exception.lvl19 */, _Fi/* s3Kch */);});
      break;
    case 1:
      return new F(function(){return _7/* GHC.Base.++ */(_F6/* GHC.IO.Exception.lvl18 */, _Fi/* s3Kch */);});
      break;
    case 2:
      return new F(function(){return _7/* GHC.Base.++ */(_F5/* GHC.IO.Exception.lvl17 */, _Fi/* s3Kch */);});
      break;
    case 3:
      return new F(function(){return _7/* GHC.Base.++ */(_F4/* GHC.IO.Exception.lvl16 */, _Fi/* s3Kch */);});
      break;
    case 4:
      return new F(function(){return _7/* GHC.Base.++ */(_F3/* GHC.IO.Exception.lvl15 */, _Fi/* s3Kch */);});
      break;
    case 5:
      return new F(function(){return _7/* GHC.Base.++ */(_F2/* GHC.IO.Exception.lvl14 */, _Fi/* s3Kch */);});
      break;
    case 6:
      return new F(function(){return _7/* GHC.Base.++ */(_F1/* GHC.IO.Exception.lvl13 */, _Fi/* s3Kch */);});
      break;
    case 7:
      return new F(function(){return _7/* GHC.Base.++ */(_F0/* GHC.IO.Exception.lvl12 */, _Fi/* s3Kch */);});
      break;
    case 8:
      return new F(function(){return _7/* GHC.Base.++ */(_EZ/* GHC.IO.Exception.lvl11 */, _Fi/* s3Kch */);});
      break;
    case 9:
      return new F(function(){return _7/* GHC.Base.++ */(_EY/* GHC.IO.Exception.lvl10 */, _Fi/* s3Kch */);});
      break;
    case 10:
      return new F(function(){return _7/* GHC.Base.++ */(_Ff/* GHC.IO.Exception.lvl9 */, _Fi/* s3Kch */);});
      break;
    case 11:
      return new F(function(){return _7/* GHC.Base.++ */(_Fe/* GHC.IO.Exception.lvl8 */, _Fi/* s3Kch */);});
      break;
    case 12:
      return new F(function(){return _7/* GHC.Base.++ */(_Fd/* GHC.IO.Exception.lvl7 */, _Fi/* s3Kch */);});
      break;
    case 13:
      return new F(function(){return _7/* GHC.Base.++ */(_Fc/* GHC.IO.Exception.lvl6 */, _Fi/* s3Kch */);});
      break;
    case 14:
      return new F(function(){return _7/* GHC.Base.++ */(_Fb/* GHC.IO.Exception.lvl5 */, _Fi/* s3Kch */);});
      break;
    case 15:
      return new F(function(){return _7/* GHC.Base.++ */(_Fa/* GHC.IO.Exception.lvl4 */, _Fi/* s3Kch */);});
      break;
    case 16:
      return new F(function(){return _7/* GHC.Base.++ */(_F9/* GHC.IO.Exception.lvl3 */, _Fi/* s3Kch */);});
      break;
    case 17:
      return new F(function(){return _7/* GHC.Base.++ */(_F8/* GHC.IO.Exception.lvl2 */, _Fi/* s3Kch */);});
      break;
    default:
      return new F(function(){return _7/* GHC.Base.++ */(_EX/* GHC.IO.Exception.lvl1 */, _Fi/* s3Kch */);});
  }
},
_Fj/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_Fk/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_Fl/* $w$cshowsPrec2 */ = function(_Fm/* s3Kcp */, _Fn/* s3Kcq */, _Fo/* s3Kcr */, _Fp/* s3Kcs */, _Fq/* s3Kct */, _Fr/* s3Kcu */){
  var _Fs/* s3Kcv */ = new T(function(){
    var _Ft/* s3Kcw */ = new T(function(){
      var _Fu/* s3KcC */ = new T(function(){
        var _Fv/* s3Kcx */ = E(_Fp/* s3Kcs */);
        if(!_Fv/* s3Kcx */._){
          return E(_Fr/* s3Kcu */);
        }else{
          var _Fw/* s3KcB */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_Fv/* s3Kcx */, new T(function(){
              return B(_7/* GHC.Base.++ */(_EV/* GHC.IO.Exception.$fExceptionIOException1 */, _Fr/* s3Kcu */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(_EW/* GHC.IO.Exception.$fExceptionIOException2 */, _Fw/* s3KcB */));
        }
      },1);
      return B(_Fg/* GHC.IO.Exception.$w$cshowsPrec3 */(_Fn/* s3Kcq */, _Fu/* s3KcC */));
    }),
    _Fx/* s3KcD */ = E(_Fo/* s3Kcr */);
    if(!_Fx/* s3KcD */._){
      return E(_Ft/* s3Kcw */);
    }else{
      return B(_7/* GHC.Base.++ */(_Fx/* s3KcD */, new T(function(){
        return B(_7/* GHC.Base.++ */(_EU/* GHC.IO.Exception.$fExceptionArrayException2 */, _Ft/* s3Kcw */));
      },1)));
    }
  }),
  _Fy/* s3KcH */ = E(_Fq/* s3Kct */);
  if(!_Fy/* s3KcH */._){
    var _Fz/* s3KcI */ = E(_Fm/* s3Kcp */);
    if(!_Fz/* s3KcI */._){
      return E(_Fs/* s3Kcv */);
    }else{
      var _FA/* s3KcK */ = E(_Fz/* s3KcI */.a);
      if(!_FA/* s3KcK */._){
        var _FB/* s3KcP */ = new T(function(){
          var _FC/* s3KcO */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_Fj/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_7/* GHC.Base.++ */(_EU/* GHC.IO.Exception.$fExceptionArrayException2 */, _Fs/* s3Kcv */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(_FA/* s3KcK */.a, _FC/* s3KcO */));
        },1);
        return new F(function(){return _7/* GHC.Base.++ */(_Fk/* GHC.IO.Handle.Types.showHandle2 */, _FB/* s3KcP */);});
      }else{
        var _FD/* s3KcV */ = new T(function(){
          var _FE/* s3KcU */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_Fj/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_7/* GHC.Base.++ */(_EU/* GHC.IO.Exception.$fExceptionArrayException2 */, _Fs/* s3Kcv */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(_FA/* s3KcK */.a, _FE/* s3KcU */));
        },1);
        return new F(function(){return _7/* GHC.Base.++ */(_Fk/* GHC.IO.Handle.Types.showHandle2 */, _FD/* s3KcV */);});
      }
    }
  }else{
    return new F(function(){return _7/* GHC.Base.++ */(_Fy/* s3KcH */.a, new T(function(){
      return B(_7/* GHC.Base.++ */(_EU/* GHC.IO.Exception.$fExceptionArrayException2 */, _Fs/* s3Kcv */));
    },1));});
  }
},
_FF/* $fExceptionIOException_$cshow */ = function(_FG/* s3Kd8 */){
  var _FH/* s3Kd9 */ = E(_FG/* s3Kd8 */);
  return new F(function(){return _Fl/* GHC.IO.Exception.$w$cshowsPrec2 */(_FH/* s3Kd9 */.a, _FH/* s3Kd9 */.b, _FH/* s3Kd9 */.c, _FH/* s3Kd9 */.d, _FH/* s3Kd9 */.f, _k/* GHC.Types.[] */);});
},
_FI/* $fExceptionIOException_$ctoException */ = function(_FJ/* B1 */){
  return new T2(0,_FK/* GHC.IO.Exception.$fExceptionIOException */,_FJ/* B1 */);
},
_FL/* $fExceptionIOException_$cshowsPrec */ = function(_FM/* s3KcY */, _FN/* s3KcZ */, _FO/* s3Kd0 */){
  var _FP/* s3Kd1 */ = E(_FN/* s3KcZ */);
  return new F(function(){return _Fl/* GHC.IO.Exception.$w$cshowsPrec2 */(_FP/* s3Kd1 */.a, _FP/* s3Kd1 */.b, _FP/* s3Kd1 */.c, _FP/* s3Kd1 */.d, _FP/* s3Kd1 */.f, _FO/* s3Kd0 */);});
},
_FQ/* $s$dmshow9 */ = function(_FR/* s3Kdg */, _FS/* s3Kdh */){
  var _FT/* s3Kdi */ = E(_FR/* s3Kdg */);
  return new F(function(){return _Fl/* GHC.IO.Exception.$w$cshowsPrec2 */(_FT/* s3Kdi */.a, _FT/* s3Kdi */.b, _FT/* s3Kdi */.c, _FT/* s3Kdi */.d, _FT/* s3Kdi */.f, _FS/* s3Kdh */);});
},
_FU/* $fShowIOException_$cshowList */ = function(_FV/* s3Kdp */, _FW/* s3Kdq */){
  return new F(function(){return _5s/* GHC.Show.showList__ */(_FQ/* GHC.IO.Exception.$s$dmshow9 */, _FV/* s3Kdp */, _FW/* s3Kdq */);});
},
_FX/* $fShowIOException */ = new T3(0,_FL/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_FF/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_FU/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_FK/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_EP/* GHC.IO.Exception.$fExceptionIOException3 */,_FX/* GHC.IO.Exception.$fShowIOException */,_FI/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_ER/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_FF/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_FY/* $fxExceptionIOException */ = new T(function(){
  return E(_FK/* GHC.IO.Exception.$fExceptionIOException */);
}),
_FZ/* UserError */ = 7,
_G0/* userError */ = function(_G1/* s3K6P */){
  return new T6(0,_4y/* GHC.Base.Nothing */,_FZ/* GHC.IO.Exception.UserError */,_k/* GHC.Types.[] */,_G1/* s3K6P */,_4y/* GHC.Base.Nothing */,_4y/* GHC.Base.Nothing */);
},
_G2/* failIO1 */ = function(_G3/* s2WaY */, _/* EXTERNAL */){
  var _G4/* s2Wb1 */ = new T(function(){
    return B(A2(_9l/* GHC.Exception.toException */,_FY/* GHC.IO.Exception.$fxExceptionIOException */, new T(function(){
      return B(A1(_G0/* GHC.IO.Exception.userError */,_G3/* s2WaY */));
    })));
  });
  return new F(function(){return die/* EXTERNAL */(_G4/* s2Wb1 */);});
},
_G5/* failIO */ = function(_G6/* B2 */, _/* EXTERNAL */){
  return new F(function(){return _G2/* GHC.IO.failIO1 */(_G6/* B2 */, _/* EXTERNAL */);});
},
_G7/* $fMonadIO_$cfail */ = function(_G8/* s3ek */){
  return new F(function(){return A1(_G5/* GHC.IO.failIO */,_G8/* s3ek */);});
},
_G9/* bindIO1 */ = function(_Ga/* s3g9 */, _Gb/* s3ga */, _/* EXTERNAL */){
  var _Gc/* s3gc */ = B(A1(_Ga/* s3g9 */,_/* EXTERNAL */));
  return new F(function(){return A2(_Gb/* s3ga */,_Gc/* s3gc */, _/* EXTERNAL */);});
},
_Gd/* $fMonadIO */ = new T5(0,_EJ/* GHC.Base.$fApplicativeIO */,_G9/* GHC.Base.bindIO1 */,_EF/* GHC.Base.thenIO1 */,_ED/* GHC.Base.returnIO1 */,_G7/* GHC.Base.$fMonadIO_$cfail */),
_Ge/* $fMonadIOIO */ = new T2(0,_Gd/* GHC.Base.$fMonadIO */,_bL/* GHC.Base.id */),
_Gf/* POST */ = 1,
_Gg/* $fToAnyMethod1 */ = "POST",
_Gh/* $fToAnyMethod2 */ = "GET",
_Gi/* lvl2 */ = "=",
_Gj/* lvl3 */ = "&",
_Gk/* toJSString */ = function(_Gl/* s3zz */){
  return E(E(_Gl/* s3zz */).a);
},
_Gm/* $wtoQueryString */ = function(_Gn/* sd4I */, _Go/* sd4J */, _Gp/* sd4K */){
  var _Gq/* sd50 */ = function(_Gr/* sd4L */){
    var _Gs/* sd4M */ = E(_Gr/* sd4L */);
    return new F(function(){return jsCat/* EXTERNAL */(new T2(1,new T(function(){
      return B(A2(_Gk/* Haste.Prim.JSType.toJSString */,_Gn/* sd4I */, _Gs/* sd4M */.a));
    }),new T2(1,new T(function(){
      return B(A2(_Gk/* Haste.Prim.JSType.toJSString */,_Go/* sd4J */, _Gs/* sd4M */.b));
    }),_k/* GHC.Types.[] */)), E(_Gi/* Haste.Ajax.lvl2 */));});
  },
  _Gt/* sd56 */ = jsCat/* EXTERNAL */(B(_8G/* GHC.Base.map */(_Gq/* sd50 */, _Gp/* sd4K */)), E(_Gj/* Haste.Ajax.lvl3 */));
  return E(_Gt/* sd56 */);
},
_Gu/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");
}),
_Gv/* fromJSString */ = function(_Gw/* s3zD */){
  return E(E(_Gw/* s3zD */).b);
},
_Gx/* liftIO */ = function(_Gy/* stz */){
  return E(E(_Gy/* stz */).b);
},
_Gz/* lvl */ = new T(function(){
  return toJSStr/* EXTERNAL */(_k/* GHC.Types.[] */);
}),
_GA/* lvl1 */ = "?",
_GB/* ajaxRequest */ = function(_GC/* sd5x */, _GD/* sd5y */, _GE/* sd5z */, _GF/* sd5A */, _GG/* sd5B */, _GH/* sd5C */, _GI/* sd5D */, _GJ/* sd5E */){
  var _GK/* sd5H */ = new T(function(){
    return B(_Gm/* Haste.Ajax.$wtoQueryString */(_GD/* sd5y */, _GE/* sd5z */, _GI/* sd5D */));
  }),
  _GL/* sd5F */ = new T(function(){
    return B(_Eh/* GHC.HastePrim.toJSStr1 */(_GH/* sd5C */));
  }),
  _GM/* sd70 */ = function(_/* EXTERNAL */){
    var _GN/* sd5M */ = function(_GO/* sd5N */){
      var _GP/* sd5O */ = function(_GQ/* sd5P */){
        var _GR/* sd5Q */ = function(_GS/* sd5R */){
          var _GT/* sd5S */ = new T(function(){
            return B(_Gv/* Haste.Prim.JSType.fromJSString */(_GF/* sd5A */));
          }),
          _GU/* sd6d */ = function(_GV/* sd5T */, _/* EXTERNAL */){
            var _GW/* sd69 */ = new T(function(){
              var _GX/* sd5V */ = E(_GV/* sd5T */),
              _GY/* sd60 */ = __eq/* EXTERNAL */(_GX/* sd5V */, E(_1p/* Haste.Prim.Any.jsNull */));
              if(!E(_GY/* sd60 */)){
                return B(A1(_GT/* sd5S */,new T(function(){
                  return String/* EXTERNAL */(_GX/* sd5V */);
                })));
              }else{
                return __Z/* EXTERNAL */;
              }
            }),
            _GZ/* sd6a */ = B(A2(_GJ/* sd5E */,_GW/* sd69 */, _/* EXTERNAL */));
            return _1p/* Haste.Prim.Any.jsNull */;
          },
          _H0/* sd6h */ = __createJSFunc/* EXTERNAL */(2, E(_GU/* sd6d */)),
          _H1/* sd6p */ = __app5/* EXTERNAL */(E(_Gu/* Haste.Ajax.f1 */), _GO/* sd5N */, _GQ/* sd5P */, true, _GS/* sd5R */, _H0/* sd6h */);
          return _0/* GHC.Tuple.() */;
        };
        if(!E(_GG/* sd5B */)){
          return new F(function(){return _GR/* sd5Q */(E(_Gz/* Haste.Ajax.lvl */));});
        }else{
          var _H2/* sd6v */ = E(_GI/* sd5D */);
          if(!_H2/* sd6v */._){
            return new F(function(){return _GR/* sd5Q */(E(_Gz/* Haste.Ajax.lvl */));});
          }else{
            return new F(function(){return _GR/* sd5Q */(B(_Gm/* Haste.Ajax.$wtoQueryString */(_GD/* sd5y */, _GE/* sd5z */, _H2/* sd6v */)));});
          }
        }
      };
      if(!E(_GG/* sd5B */)){
        if(!E(_GI/* sd5D */)._){
          return new F(function(){return _GP/* sd5O */(toJSStr/* EXTERNAL */(E(_GH/* sd5C */)));});
        }else{
          var _H3/* sd6N */ = jsCat/* EXTERNAL */(new T2(1,_GL/* sd5F */,new T2(1,_GK/* sd5H */,_k/* GHC.Types.[] */)), E(_GA/* Haste.Ajax.lvl1 */));
          return new F(function(){return _GP/* sd5O */(_H3/* sd6N */);});
        }
      }else{
        return new F(function(){return _GP/* sd5O */(toJSStr/* EXTERNAL */(E(_GH/* sd5C */)));});
      }
    };
    if(!E(_GG/* sd5B */)){
      return new F(function(){return _GN/* sd5M */(E(_Gh/* Haste.Ajax.$fToAnyMethod2 */));});
    }else{
      return new F(function(){return _GN/* sd5M */(E(_Gg/* Haste.Ajax.$fToAnyMethod1 */));});
    }
  };
  return new F(function(){return A2(_Gx/* Control.Monad.IO.Class.liftIO */,_GC/* sd5x */, _GM/* sd70 */);});
},
_H4/* bookAckTxt2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/crc-logo.png\' alt=\'CRC logo\'/>      </a>   </p>"));
}),
_H5/* bookAckTxt1 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_E4/* Config.Config.staticURL */, _H4/* Texts.bookAckTxt2 */));
}),
_H6/* bookAckTxt */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<hr/>   <p>     (*) With kind permission of     <a href=\'http://taylorandfrancis.com/\' target=\'_blank\'>       <img src=\'", _H5/* Texts.bookAckTxt1 */));
}),
_H7/* bookLabelTxt1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": </h1>"));
}),
_H8/* bookLabelTxt2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h1>   <a href=\'https://www.crcpress.com/Data-Stewardship-for-Discovery-A-Practical-Guide-for-Data-Experts/Mons/p/book/9781498753173\' target=\'_blank\'>Book</a>   (*) chapter "));
}),
_H9/* readEither4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.read: no parse"));
}),
_Ha/* lvl */ = new T(function(){
  return B(err/* EXTERNAL */(_H9/* Text.Read.readEither4 */));
}),
_Hb/* readEither2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.read: ambiguous parse"));
}),
_Hc/* lvl1 */ = new T(function(){
  return B(err/* EXTERNAL */(_Hb/* Text.Read.readEither2 */));
}),
_Hd/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("api/getQuestion"));
}),
_He/* lvl17 */ = "chid",
_Hf/* lvl18 */ = "qid",
_Hg/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("api/getBookContents"));
}),
_Hh/* $fReadMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just"));
}),
_Hi/* $fReadMaybe4 */ = 11,
_Hj/* $fReadMaybe5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_Hk/* readPrec */ = function(_Hl/* s1vgA */){
  return E(E(_Hl/* s1vgA */).c);
},
_Hm/* $fReadMaybe2 */ = function(_Hn/* s1vrp */, _Ho/* s1vrq */){
  var _Hp/* s1vrr */ = new T(function(){
    return B(_Hk/* GHC.Read.readPrec */(_Hn/* s1vrp */));
  }),
  _Hq/* s1vrZ */ = function(_Hr/* s1vrs */, _Hs/* s1vrt */){
    var _Ht/* s1vru */ = new T(function(){
      var _Hu/* s1vrv */ = new T(function(){
        return B(A1(_Hs/* s1vrt */,_4y/* GHC.Base.Nothing */));
      });
      return B(_lk/* Text.Read.Lex.expect2 */(function(_Hv/* s1vrw */){
        var _Hw/* s1vrx */ = E(_Hv/* s1vrw */);
        return (_Hw/* s1vrx */._==3) ? (!B(_2n/* GHC.Base.eqString */(_Hw/* s1vrx */.a, _Hj/* GHC.Read.$fReadMaybe5 */))) ? new T0(2) : E(_Hu/* s1vrv */) : new T0(2);
      }));
    }),
    _Hx/* s1vrB */ = function(_Hy/* s1vrC */){
      return E(_Ht/* s1vru */);
    },
    _Hz/* s1vrY */ = new T(function(){
      if(E(_Hr/* s1vrs */)>10){
        return new T0(2);
      }else{
        var _HA/* s1vrK */ = new T(function(){
          var _HB/* s1vrL */ = new T(function(){
            return B(A2(_Hp/* s1vrr */,_Hi/* GHC.Read.$fReadMaybe4 */, function(_HC/* s1vrM */){
              return new F(function(){return A1(_Hs/* s1vrt */,new T1(1,_HC/* s1vrM */));});
            }));
          });
          return B(_lk/* Text.Read.Lex.expect2 */(function(_HD/* s1vrP */){
            var _HE/* s1vrQ */ = E(_HD/* s1vrP */);
            return (_HE/* s1vrQ */._==3) ? (!B(_2n/* GHC.Base.eqString */(_HE/* s1vrQ */.a, _Hh/* GHC.Read.$fReadMaybe3 */))) ? new T0(2) : E(_HB/* s1vrL */) : new T0(2);
          }));
        }),
        _HF/* s1vrU */ = function(_HG/* s1vrV */){
          return E(_HA/* s1vrK */);
        };
        return new T1(1,function(_HH/* s1vrW */){
          return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_HH/* s1vrW */, _HF/* s1vrU */);});
        });
      }
    });
    return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_HI/* s1vrD */){
      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_HI/* s1vrD */, _Hx/* s1vrB */);});
    }), _Hz/* s1vrY */);});
  };
  return new F(function(){return _mb/* GHC.Read.$fReadDouble10 */(_Hq/* s1vrZ */, _Ho/* s1vrq */);});
},
_HJ/* a2 */ = function(_HK/* s1vnB */, _HL/* s1vnC */){
  return new F(function(){return _HM/* GHC.Read.$wa20 */(_HL/* s1vnC */);});
},
_HM/* $wa20 */ = function(_HN/* s1vnD */){
  var _HO/* s1vnI */ = new T(function(){
    return B(_lk/* Text.Read.Lex.expect2 */(function(_HP/* s1vnF */){
      var _HQ/* s1vnG */ = E(_HP/* s1vnF */);
      if(!_HQ/* s1vnG */._){
        return new F(function(){return A1(_HN/* s1vnD */,_HQ/* s1vnG */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _HR/* s1vnJ */ = function(_HS/* s1vnK */){
    return E(_HO/* s1vnI */);
  };
  return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_HT/* s1vnL */){
    return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_HT/* s1vnL */, _HR/* s1vnJ */);});
  }), new T(function(){
    return new T1(1,B(_lS/* GHC.Read.$wa3 */(_HJ/* GHC.Read.a2 */, _HN/* s1vnD */)));
  }));});
},
_HU/* $fReadChar2 */ = function(_HV/* s1vnR */, _HW/* s1vnS */){
  return new F(function(){return _HM/* GHC.Read.$wa20 */(_HW/* s1vnS */);});
},
_HX/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("["));
}),
_HY/* $wa */ = function(_HZ/* s1vjF */, _I0/* s1vjG */){
  var _I1/* s1vjH */ = function(_I2/* s1vjI */, _I3/* s1vjJ */){
    var _I4/* s1vjK */ = new T(function(){
      return B(A1(_I3/* s1vjJ */,_k/* GHC.Types.[] */));
    }),
    _I5/* s1vjL */ = new T(function(){
      var _I6/* s1vjQ */ = function(_I7/* s1vjM */){
        return new F(function(){return _I1/* s1vjH */(_8F/* GHC.Types.True */, function(_I8/* s1vjN */){
          return new F(function(){return A1(_I3/* s1vjJ */,new T2(1,_I7/* s1vjM */,_I8/* s1vjN */));});
        });});
      };
      return B(A2(_HZ/* s1vjF */,_lR/* Text.ParserCombinators.ReadPrec.minPrec */, _I6/* s1vjQ */));
    }),
    _I9/* s1vk8 */ = new T(function(){
      return B(_lk/* Text.Read.Lex.expect2 */(function(_Ia/* s1vjS */){
        var _Ib/* s1vjT */ = E(_Ia/* s1vjS */);
        if(_Ib/* s1vjT */._==2){
          var _Ic/* s1vjV */ = E(_Ib/* s1vjT */.a);
          if(!_Ic/* s1vjV */._){
            return new T0(2);
          }else{
            var _Id/* s1vjX */ = _Ic/* s1vjV */.b;
            switch(E(_Ic/* s1vjV */.a)){
              case 44:
                return (E(_Id/* s1vjX */)._==0) ? (!E(_I2/* s1vjI */)) ? new T0(2) : E(_I5/* s1vjL */) : new T0(2);
              case 93:
                return (E(_Id/* s1vjX */)._==0) ? E(_I4/* s1vjK */) : new T0(2);
              default:
                return new T0(2);
            }
          }
        }else{
          return new T0(2);
        }
      }));
    }),
    _Ie/* s1vk9 */ = function(_If/* s1vka */){
      return E(_I9/* s1vk8 */);
    };
    return new T1(1,function(_Ig/* s1vkb */){
      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Ig/* s1vkb */, _Ie/* s1vk9 */);});
    });
  },
  _Ih/* s1vkd */ = function(_Ii/* s1vkf */, _Ij/* s1vkg */){
    return new F(function(){return _Ik/* s1vke */(_Ij/* s1vkg */);});
  },
  _Ik/* s1vke */ = function(_Il/* s1vkh */){
    var _Im/* s1vki */ = new T(function(){
      var _In/* s1vkj */ = new T(function(){
        var _Io/* s1vkq */ = new T(function(){
          var _Ip/* s1vkp */ = function(_Iq/* s1vkl */){
            return new F(function(){return _I1/* s1vjH */(_8F/* GHC.Types.True */, function(_Ir/* s1vkm */){
              return new F(function(){return A1(_Il/* s1vkh */,new T2(1,_Iq/* s1vkl */,_Ir/* s1vkm */));});
            });});
          };
          return B(A2(_HZ/* s1vjF */,_lR/* Text.ParserCombinators.ReadPrec.minPrec */, _Ip/* s1vkp */));
        });
        return B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_I1/* s1vjH */(_4x/* GHC.Types.False */, _Il/* s1vkh */)), _Io/* s1vkq */));
      });
      return B(_lk/* Text.Read.Lex.expect2 */(function(_Is/* s1vkr */){
        var _It/* s1vks */ = E(_Is/* s1vkr */);
        return (_It/* s1vks */._==2) ? (!B(_2n/* GHC.Base.eqString */(_It/* s1vks */.a, _HX/* GHC.Read.lvl6 */))) ? new T0(2) : E(_In/* s1vkj */) : new T0(2);
      }));
    }),
    _Iu/* s1vkw */ = function(_Iv/* s1vkx */){
      return E(_Im/* s1vki */);
    };
    return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_Iw/* s1vky */){
      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Iw/* s1vky */, _Iu/* s1vkw */);});
    }), new T(function(){
      return new T1(1,B(_lS/* GHC.Read.$wa3 */(_Ih/* s1vkd */, _Il/* s1vkh */)));
    }));});
  };
  return new F(function(){return _Ik/* s1vke */(_I0/* s1vjG */);});
},
_Ix/* a7 */ = function(_Iy/* s1vpn */, _Iz/* s1vpo */){
  return new F(function(){return _IA/* GHC.Read.$wa19 */(_Iz/* s1vpo */);});
},
_IA/* $wa19 */ = function(_IB/* s1vpp */){
  var _IC/* s1vpu */ = new T(function(){
    return B(_lk/* Text.Read.Lex.expect2 */(function(_ID/* s1vpr */){
      var _IE/* s1vps */ = E(_ID/* s1vpr */);
      if(_IE/* s1vps */._==1){
        return new F(function(){return A1(_IB/* s1vpp */,_IE/* s1vps */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _IF/* s1vpv */ = function(_IG/* s1vpw */){
    return E(_IC/* s1vpu */);
  };
  return new F(function(){return _9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_9S/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_IH/* s1vpx */){
    return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_IH/* s1vpx */, _IF/* s1vpv */);});
  }), new T(function(){
    return B(_HY/* GHC.Read.$wa */(_HU/* GHC.Read.$fReadChar2 */, _IB/* s1vpp */));
  }))), new T(function(){
    return new T1(1,B(_lS/* GHC.Read.$wa3 */(_Ix/* GHC.Read.a7 */, _IB/* s1vpp */)));
  }));});
},
_II/* $fReadChar1 */ = function(_IJ/* s1vpF */, _IK/* s1vpG */){
  return new F(function(){return _IA/* GHC.Read.$wa19 */(_IK/* s1vpG */);});
},
_IL/* $fRead[]3 */ = function(_IM/* s1vpI */, _IN/* s1vpJ */){
  return new F(function(){return _HY/* GHC.Read.$wa */(_II/* GHC.Read.$fReadChar1 */, _IN/* s1vpJ */);});
},
_IO/* $fRead[]5 */ = new T(function(){
  return B(_HY/* GHC.Read.$wa */(_II/* GHC.Read.$fReadChar1 */, _aY/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_IP/* $fRead[]4 */ = function(_IQ/* B1 */){
  return new F(function(){return _8r/* Text.ParserCombinators.ReadP.run */(_IO/* GHC.Read.$fRead[]5 */, _IQ/* B1 */);});
},
_IR/* $fReadChar4 */ = new T(function(){
  return B(_IA/* GHC.Read.$wa19 */(_aY/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_IS/* $fReadChar3 */ = function(_IQ/* B1 */){
  return new F(function(){return _8r/* Text.ParserCombinators.ReadP.run */(_IR/* GHC.Read.$fReadChar4 */, _IQ/* B1 */);});
},
_IT/* $fRead[]_$s$creadsPrec1 */ = function(_IU/* s1vpH */, _IQ/* B1 */){
  return new F(function(){return _IS/* GHC.Read.$fReadChar3 */(_IQ/* B1 */);});
},
_IV/* $fRead[]_$s$fRead[]1 */ = new T4(0,_IT/* GHC.Read.$fRead[]_$s$creadsPrec1 */,_IP/* GHC.Read.$fRead[]4 */,_II/* GHC.Read.$fReadChar1 */,_IL/* GHC.Read.$fRead[]3 */),
_IW/* $fShowQuestion2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_IX/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_IY/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("otherInfo"));
}),
_IZ/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(","));
}),
_J0/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("bookRef"));
}),
_J1/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("questionId"));
}),
_J2/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("chapterId"));
}),
_J3/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{"));
}),
_J4/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Question"));
}),
_J5/* $wa */ = function(_J6/* s3GF */, _J7/* s3GG */){
  if(_J6/* s3GF */>11){
    return new T0(2);
  }else{
    var _J8/* s3GJ */ = new T(function(){
      var _J9/* s3GK */ = new T(function(){
        var _Ja/* s3GL */ = new T(function(){
          var _Jb/* s3GM */ = new T(function(){
            var _Jc/* s3GN */ = new T(function(){
              var _Jd/* s3II */ = function(_Je/* s3GO */){
                var _Jf/* s3GP */ = new T(function(){
                  var _Jg/* s3GQ */ = new T(function(){
                    var _Jh/* s3GR */ = new T(function(){
                      var _Ji/* s3GS */ = new T(function(){
                        var _Jj/* s3Ie */ = function(_Jk/* s3GT */){
                          var _Jl/* s3GU */ = new T(function(){
                            var _Jm/* s3GV */ = new T(function(){
                              var _Jn/* s3GW */ = new T(function(){
                                var _Jo/* s3GX */ = new T(function(){
                                  var _Jp/* s3HK */ = function(_Jq/* s3GY */){
                                    var _Jr/* s3GZ */ = new T(function(){
                                      var _Js/* s3H0 */ = new T(function(){
                                        var _Jt/* s3H1 */ = new T(function(){
                                          var _Ju/* s3H2 */ = new T(function(){
                                            var _Jv/* s3Hg */ = function(_Jw/* s3H3 */){
                                              var _Jx/* s3H4 */ = new T(function(){
                                                var _Jy/* s3H5 */ = new T(function(){
                                                  return B(A1(_J7/* s3GG */,new T4(0,_Je/* s3GO */,_Jk/* s3GT */,_Jq/* s3GY */,_Jw/* s3H3 */)));
                                                });
                                                return B(_lk/* Text.Read.Lex.expect2 */(function(_Jz/* s3H7 */){
                                                  var _JA/* s3H8 */ = E(_Jz/* s3H7 */);
                                                  return (_JA/* s3H8 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_JA/* s3H8 */.a, _IW/* Model.Question.$fShowQuestion2 */))) ? new T0(2) : E(_Jy/* s3H5 */) : new T0(2);
                                                }));
                                              }),
                                              _JB/* s3Hc */ = function(_JC/* s3Hd */){
                                                return E(_Jx/* s3H4 */);
                                              };
                                              return new T1(1,function(_JD/* s3He */){
                                                return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_JD/* s3He */, _JB/* s3Hc */);});
                                              });
                                            };
                                            return B(A3(_Hm/* GHC.Read.$fReadMaybe2 */,_IV/* GHC.Read.$fRead[]_$s$fRead[]1 */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _Jv/* s3Hg */));
                                          });
                                          return B(_lk/* Text.Read.Lex.expect2 */(function(_JE/* s3Hh */){
                                            var _JF/* s3Hi */ = E(_JE/* s3Hh */);
                                            return (_JF/* s3Hi */._==2) ? (!B(_2n/* GHC.Base.eqString */(_JF/* s3Hi */.a, _IX/* Model.Question.lvl */))) ? new T0(2) : E(_Ju/* s3H2 */) : new T0(2);
                                          }));
                                        }),
                                        _JG/* s3Hm */ = function(_JH/* s3Hn */){
                                          return E(_Jt/* s3H1 */);
                                        },
                                        _JI/* s3Ho */ = function(_JJ/* s3Hp */){
                                          return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_JJ/* s3Hp */, _JG/* s3Hm */);});
                                        };
                                        return B(_lk/* Text.Read.Lex.expect2 */(function(_JK/* s3Hr */){
                                          var _JL/* s3Hs */ = E(_JK/* s3Hr */);
                                          return (_JL/* s3Hs */._==3) ? (!B(_2n/* GHC.Base.eqString */(_JL/* s3Hs */.a, _IY/* Model.Question.lvl1 */))) ? new T0(2) : E(new T1(1,_JI/* s3Ho */)) : new T0(2);
                                        }));
                                      }),
                                      _JM/* s3Hw */ = function(_JN/* s3Hx */){
                                        return E(_Js/* s3H0 */);
                                      },
                                      _JO/* s3Hy */ = function(_JP/* s3Hz */){
                                        return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_JP/* s3Hz */, _JM/* s3Hw */);});
                                      };
                                      return B(_lk/* Text.Read.Lex.expect2 */(function(_JQ/* s3HB */){
                                        var _JR/* s3HC */ = E(_JQ/* s3HB */);
                                        return (_JR/* s3HC */._==2) ? (!B(_2n/* GHC.Base.eqString */(_JR/* s3HC */.a, _IZ/* Model.Question.lvl2 */))) ? new T0(2) : E(new T1(1,_JO/* s3Hy */)) : new T0(2);
                                      }));
                                    }),
                                    _JS/* s3HG */ = function(_JT/* s3HH */){
                                      return E(_Jr/* s3GZ */);
                                    };
                                    return new T1(1,function(_JU/* s3HI */){
                                      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_JU/* s3HI */, _JS/* s3HG */);});
                                    });
                                  };
                                  return B(A3(_Hm/* GHC.Read.$fReadMaybe2 */,_IV/* GHC.Read.$fRead[]_$s$fRead[]1 */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _Jp/* s3HK */));
                                });
                                return B(_lk/* Text.Read.Lex.expect2 */(function(_JV/* s3HL */){
                                  var _JW/* s3HM */ = E(_JV/* s3HL */);
                                  return (_JW/* s3HM */._==2) ? (!B(_2n/* GHC.Base.eqString */(_JW/* s3HM */.a, _IX/* Model.Question.lvl */))) ? new T0(2) : E(_Jo/* s3GX */) : new T0(2);
                                }));
                              }),
                              _JX/* s3HQ */ = function(_JY/* s3HR */){
                                return E(_Jn/* s3GW */);
                              },
                              _JZ/* s3HS */ = function(_K0/* s3HT */){
                                return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_K0/* s3HT */, _JX/* s3HQ */);});
                              };
                              return B(_lk/* Text.Read.Lex.expect2 */(function(_K1/* s3HV */){
                                var _K2/* s3HW */ = E(_K1/* s3HV */);
                                return (_K2/* s3HW */._==3) ? (!B(_2n/* GHC.Base.eqString */(_K2/* s3HW */.a, _J0/* Model.Question.lvl3 */))) ? new T0(2) : E(new T1(1,_JZ/* s3HS */)) : new T0(2);
                              }));
                            }),
                            _K3/* s3I0 */ = function(_K4/* s3I1 */){
                              return E(_Jm/* s3GV */);
                            },
                            _K5/* s3I2 */ = function(_K6/* s3I3 */){
                              return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_K6/* s3I3 */, _K3/* s3I0 */);});
                            };
                            return B(_lk/* Text.Read.Lex.expect2 */(function(_K7/* s3I5 */){
                              var _K8/* s3I6 */ = E(_K7/* s3I5 */);
                              return (_K8/* s3I6 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_K8/* s3I6 */.a, _IZ/* Model.Question.lvl2 */))) ? new T0(2) : E(new T1(1,_K5/* s3I2 */)) : new T0(2);
                            }));
                          }),
                          _K9/* s3Ia */ = function(_Ka/* s3Ib */){
                            return E(_Jl/* s3GU */);
                          };
                          return new T1(1,function(_Kb/* s3Ic */){
                            return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Kb/* s3Ic */, _K9/* s3Ia */);});
                          });
                        };
                        return B(A3(_mm/* GHC.Read.$fReadInt3 */,_mP/* GHC.Read.$fReadInt_$sconvertInt */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _Jj/* s3Ie */));
                      });
                      return B(_lk/* Text.Read.Lex.expect2 */(function(_Kc/* s3If */){
                        var _Kd/* s3Ig */ = E(_Kc/* s3If */);
                        return (_Kd/* s3Ig */._==2) ? (!B(_2n/* GHC.Base.eqString */(_Kd/* s3Ig */.a, _IX/* Model.Question.lvl */))) ? new T0(2) : E(_Ji/* s3GS */) : new T0(2);
                      }));
                    }),
                    _Ke/* s3Ik */ = function(_Kf/* s3Il */){
                      return E(_Jh/* s3GR */);
                    },
                    _Kg/* s3Im */ = function(_Kh/* s3In */){
                      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Kh/* s3In */, _Ke/* s3Ik */);});
                    };
                    return B(_lk/* Text.Read.Lex.expect2 */(function(_Ki/* s3Ip */){
                      var _Kj/* s3Iq */ = E(_Ki/* s3Ip */);
                      return (_Kj/* s3Iq */._==3) ? (!B(_2n/* GHC.Base.eqString */(_Kj/* s3Iq */.a, _J1/* Model.Question.lvl4 */))) ? new T0(2) : E(new T1(1,_Kg/* s3Im */)) : new T0(2);
                    }));
                  }),
                  _Kk/* s3Iu */ = function(_Kl/* s3Iv */){
                    return E(_Jg/* s3GQ */);
                  },
                  _Km/* s3Iw */ = function(_Kn/* s3Ix */){
                    return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Kn/* s3Ix */, _Kk/* s3Iu */);});
                  };
                  return B(_lk/* Text.Read.Lex.expect2 */(function(_Ko/* s3Iz */){
                    var _Kp/* s3IA */ = E(_Ko/* s3Iz */);
                    return (_Kp/* s3IA */._==2) ? (!B(_2n/* GHC.Base.eqString */(_Kp/* s3IA */.a, _IZ/* Model.Question.lvl2 */))) ? new T0(2) : E(new T1(1,_Km/* s3Iw */)) : new T0(2);
                  }));
                }),
                _Kq/* s3IE */ = function(_Kr/* s3IF */){
                  return E(_Jf/* s3GP */);
                };
                return new T1(1,function(_Ks/* s3IG */){
                  return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Ks/* s3IG */, _Kq/* s3IE */);});
                });
              };
              return B(A3(_mm/* GHC.Read.$fReadInt3 */,_mP/* GHC.Read.$fReadInt_$sconvertInt */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _Jd/* s3II */));
            });
            return B(_lk/* Text.Read.Lex.expect2 */(function(_Kt/* s3IJ */){
              var _Ku/* s3IK */ = E(_Kt/* s3IJ */);
              return (_Ku/* s3IK */._==2) ? (!B(_2n/* GHC.Base.eqString */(_Ku/* s3IK */.a, _IX/* Model.Question.lvl */))) ? new T0(2) : E(_Jc/* s3GN */) : new T0(2);
            }));
          }),
          _Kv/* s3IO */ = function(_Kw/* s3IP */){
            return E(_Jb/* s3GM */);
          },
          _Kx/* s3IQ */ = function(_Ky/* s3IR */){
            return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Ky/* s3IR */, _Kv/* s3IO */);});
          };
          return B(_lk/* Text.Read.Lex.expect2 */(function(_Kz/* s3IT */){
            var _KA/* s3IU */ = E(_Kz/* s3IT */);
            return (_KA/* s3IU */._==3) ? (!B(_2n/* GHC.Base.eqString */(_KA/* s3IU */.a, _J2/* Model.Question.lvl5 */))) ? new T0(2) : E(new T1(1,_Kx/* s3IQ */)) : new T0(2);
          }));
        }),
        _KB/* s3IY */ = function(_KC/* s3IZ */){
          return E(_Ja/* s3GL */);
        },
        _KD/* s3J0 */ = function(_KE/* s3J1 */){
          return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KE/* s3J1 */, _KB/* s3IY */);});
        };
        return B(_lk/* Text.Read.Lex.expect2 */(function(_KF/* s3J3 */){
          var _KG/* s3J4 */ = E(_KF/* s3J3 */);
          return (_KG/* s3J4 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_KG/* s3J4 */.a, _J3/* Model.Question.lvl6 */))) ? new T0(2) : E(new T1(1,_KD/* s3J0 */)) : new T0(2);
        }));
      }),
      _KH/* s3J8 */ = function(_KI/* s3J9 */){
        return E(_J9/* s3GK */);
      },
      _KJ/* s3Ja */ = function(_KK/* s3Jb */){
        return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KK/* s3Jb */, _KH/* s3J8 */);});
      };
      return B(_lk/* Text.Read.Lex.expect2 */(function(_KL/* s3Jd */){
        var _KM/* s3Je */ = E(_KL/* s3Jd */);
        return (_KM/* s3Je */._==3) ? (!B(_2n/* GHC.Base.eqString */(_KM/* s3Je */.a, _J4/* Model.Question.lvl7 */))) ? new T0(2) : E(new T1(1,_KJ/* s3Ja */)) : new T0(2);
      }));
    }),
    _KN/* s3Ji */ = function(_KO/* s3Jj */){
      return E(_J8/* s3GJ */);
    };
    return new T1(1,function(_KP/* s3Jk */){
      return new F(function(){return A2(_k1/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KP/* s3Jk */, _KN/* s3Ji */);});
    });
  }
},
_KQ/* $fReadQuestion3 */ = function(_KR/* s3Jm */, _KS/* s3Jn */){
  return new F(function(){return _J5/* Model.Question.$wa */(E(_KR/* s3Jm */), _KS/* s3Jn */);});
},
_KT/* lvl2 */ = new T(function(){
  return B(A3(_mb/* GHC.Read.$fReadDouble10 */,_KQ/* Model.Question.$fReadQuestion3 */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _mW/* Text.Read.readEither5 */));
}),
_KU/* $wa33 */ = function(_KV/* skkL */, _KW/* skkM */, _/* EXTERNAL */){
  var _KX/* skkW */ = eval/* EXTERNAL */(E(_11/* FormEngine.JQuery.setText2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_KX/* skkW */), toJSStr/* EXTERNAL */(E(_KV/* skkL */)), _KW/* skkM */);});
},
_KY/* a */ = new T(function(){
  return B(unCStr/* EXTERNAL */("div"));
}),
_KZ/* getHeight_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.height(); })");
}),
_L0/* getScrollTop_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.scrollTop(); })");
}),
_L1/* hideJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_L2/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("body"));
}),
_L3/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_L4/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No details available"));
}),
_L5/* overlayId */ = new T(function(){
  return B(unCStr/* EXTERNAL */("overlay"));
}),
_L6/* selectById2 */ = "(function (id) { return $(\'#\' + id); })",
_L7/* selectById1 */ = function(_L8/* sk9z */, _/* EXTERNAL */){
  var _L9/* sk9J */ = eval/* EXTERNAL */(E(_L6/* FormEngine.JQuery.selectById2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_L9/* sk9J */), toJSStr/* EXTERNAL */(E(_L8/* sk9z */)));});
},
_La/* setHeight_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (val, jq) { jq.height(val); return jq; })");
}),
_Lb/* showJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visible"));
}),
_Lc/* overlayOn1 */ = function(_Ld/* s37P */, _/* EXTERNAL */){
  var _Le/* s37R */ = B(_L7/* FormEngine.JQuery.selectById1 */(_L5/* Overlay.overlayId */, _/* EXTERNAL */)),
  _Lf/* s37U */ = E(_Le/* s37R */),
  _Lg/* s37W */ = B(_sY/* FormEngine.JQuery.$wa9 */(_KY/* Overlay.a */, _Lf/* s37U */, _/* EXTERNAL */)),
  _Lh/* s37Z */ = function(_/* EXTERNAL */){
    var _Li/* s381 */ = B(_2E/* FormEngine.JQuery.select1 */(_L2/* Overlay.lvl */, _/* EXTERNAL */)),
    _Lj/* s389 */ = __app1/* EXTERNAL */(E(_KZ/* FormEngine.JQuery.getHeight_f1 */), E(_Li/* s381 */)),
    _Lk/* s38d */ = Number/* EXTERNAL */(_Lj/* s389 */),
    _Ll/* s38h */ = jsTrunc/* EXTERNAL */(_Lk/* s38d */),
    _Lm/* s38p */ = __app2/* EXTERNAL */(E(_La/* FormEngine.JQuery.setHeight_f1 */), _Ll/* s38h */, _Lf/* s37U */),
    _Ln/* s38s */ = B(_sY/* FormEngine.JQuery.$wa9 */(_KY/* Overlay.a */, _Lf/* s37U */, _/* EXTERNAL */)),
    _Lo/* s38v */ = B(_2E/* FormEngine.JQuery.select1 */(_L2/* Overlay.lvl */, _/* EXTERNAL */)),
    _Lp/* s38D */ = __app1/* EXTERNAL */(E(_L0/* FormEngine.JQuery.getScrollTop_f1 */), E(_Lo/* s38v */)),
    _Lq/* s38H */ = Number/* EXTERNAL */(_Lp/* s38D */),
    _Lr/* s38L */ = jsTrunc/* EXTERNAL */(_Lq/* s38H */),
    _Ls/* s38S */ = B(_K/* FormEngine.JQuery.$wa2 */(_L3/* Overlay.lvl1 */, B(_1M/* GHC.Show.$wshowSignedInt */(0, _Lr/* s38L */+25|0, _k/* GHC.Types.[] */)), E(_Ln/* s38s */), _/* EXTERNAL */));
    return new F(function(){return _K/* FormEngine.JQuery.$wa2 */(_L1/* FormEngine.JQuery.hideJq3 */, _Lb/* FormEngine.JQuery.showJq2 */, _Lf/* s37U */, _/* EXTERNAL */);});
  },
  _Lt/* s38V */ = E(_Ld/* s37P */);
  if(!_Lt/* s38V */._){
    var _Lu/* s38Y */ = B(_KU/* FormEngine.JQuery.$wa33 */(_L4/* Overlay.lvl2 */, E(_Lg/* s37W */), _/* EXTERNAL */));
    return new F(function(){return _Lh/* s37Z */(_/* EXTERNAL */);});
  }else{
    var _Lv/* s395 */ = B(_sT/* FormEngine.JQuery.$wa26 */(_Lt/* s38V */, E(_Lg/* s37W */), _/* EXTERNAL */));
    return new F(function(){return _Lh/* s37Z */(_/* EXTERNAL */);});
  }
},
_Lw/* $wlvl */ = function(_Lx/* s4IQ */, _/* EXTERNAL */){
  var _Ly/* s4IT */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_Lx/* s4IQ */)))),
  _Lz/* s4J5 */ = E(_Ly/* s4IT */.g);
  if(!_Lz/* s4J5 */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _LA/* s4J6 */ = _Lz/* s4J5 */.a,
    _LB/* s4J7 */ = E(_Ly/* s4IT */.h);
    if(!_LB/* s4J7 */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _LC/* s4J8 */ = _LB/* s4J7 */.a,
      _LD/* s4J9 */ = new T(function(){
        return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_LA/* s4J6 */), _k/* GHC.Types.[] */));
      }),
      _LE/* s4Jd */ = new T(function(){
        return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_LC/* s4J8 */), _k/* GHC.Types.[] */));
      }),
      _LF/* s4Kp */ = function(_LG/* s4Jp */){
        var _LH/* s4Jq */ = new T(function(){
          var _LI/* s4Jr */ = E(_LG/* s4Jp */);
          if(!_LI/* s4Jr */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T1(1,new T(function(){
              var _LJ/* s4Ju */ = B(_8k/* Text.Read.readEither6 */(B(_8r/* Text.ParserCombinators.ReadP.run */(_KT/* Form.lvl2 */, _LI/* s4Jr */.a))));
              if(!_LJ/* s4Ju */._){
                return E(_Ha/* Form.lvl */);
              }else{
                if(!E(_LJ/* s4Ju */.b)._){
                  return E(_LJ/* s4Ju */.a);
                }else{
                  return E(_Hc/* Form.lvl1 */);
                }
              }
            }));
          }
        }),
        _LK/* s4JJ */ = new T2(1,new T(function(){
          var _LL/* s4JC */ = E(_LH/* s4Jq */);
          if(!_LL/* s4JC */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(E(_LL/* s4JC */.a).d);
          }
        }),_k/* GHC.Types.[] */),
        _LM/* s4JK */ = new T(function(){
          var _LN/* s4JL */ = E(_LH/* s4Jq */);
          if(!_LN/* s4JL */._){
            return __Z/* EXTERNAL */;
          }else{
            if(!E(E(_LN/* s4JL */.a).c)._){
              return __Z/* EXTERNAL */;
            }else{
              return E(_H6/* Texts.bookAckTxt */);
            }
          }
        }),
        _LO/* s4JU */ = function(_LP/* s4JV */){
          var _LQ/* s4JW */ = E(_LP/* s4JV */);
          if(!_LQ/* s4JW */._){
            return E(_LM/* s4JK */);
          }else{
            return new F(function(){return _7/* GHC.Base.++ */(_LQ/* s4JW */.a, new T(function(){
              return B(_LO/* s4JU */(_LQ/* s4JW */.b));
            },1));});
          }
        },
        _LR/* s4Ko */ = function(_LS/* s4K0 */, _/* EXTERNAL */){
          var _LT/* s4Kk */ = new T(function(){
            var _LU/* s4K2 */ = E(_LH/* s4Jq */);
            if(!_LU/* s4K2 */._){
              return B(_LO/* s4JU */(B(_pa/* Data.Maybe.catMaybes1 */(new T2(1,_LS/* s4K0 */,_LK/* s4JJ */)))));
            }else{
              var _LV/* s4Kb */ = E(E(_LU/* s4K2 */.a).c);
              if(!_LV/* s4Kb */._){
                return B(_LO/* s4JU */(B(_pa/* Data.Maybe.catMaybes1 */(new T2(1,_LS/* s4K0 */,_LK/* s4JJ */)))));
              }else{
                var _LW/* s4Kj */ = new T(function(){
                  var _LX/* s4Ki */ = new T(function(){
                    return B(_7/* GHC.Base.++ */(_H7/* Texts.bookLabelTxt1 */, new T(function(){
                      return B(_LO/* s4JU */(B(_pa/* Data.Maybe.catMaybes1 */(new T2(1,_LS/* s4K0 */,_LK/* s4JJ */)))));
                    },1)));
                  },1);
                  return B(_7/* GHC.Base.++ */(_LV/* s4Kb */.a, _LX/* s4Ki */));
                },1);
                return B(_7/* GHC.Base.++ */(_H8/* Texts.bookLabelTxt2 */, _LW/* s4Kj */));
              }
            }
          },1),
          _LY/* s4Kl */ = B(_Lc/* Overlay.overlayOn1 */(_LT/* s4Kk */, _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        };
        return new F(function(){return _GB/* Haste.Ajax.ajaxRequest */(_Ge/* Control.Monad.IO.Class.$fMonadIOIO */, _Ec/* Haste.Prim.JSType.$fJSTypeJSString */, _Ej/* Haste.Prim.JSType.$fJSType[] */, _Ej/* Haste.Prim.JSType.$fJSType[] */, _Gf/* Haste.Ajax.POST */, _Hg/* Form.lvl19 */, new T2(1,new T2(0,_He/* Form.lvl17 */,_LD/* s4J9 */),new T2(1,new T2(0,_Hf/* Form.lvl18 */,_LE/* s4Jd */),_k/* GHC.Types.[] */)), _LR/* s4Ko */);});
      };
      return new F(function(){return A(_GB/* Haste.Ajax.ajaxRequest */,[_Ge/* Control.Monad.IO.Class.$fMonadIOIO */, _Ec/* Haste.Prim.JSType.$fJSTypeJSString */, _Ej/* Haste.Prim.JSType.$fJSType[] */, _Ej/* Haste.Prim.JSType.$fJSType[] */, _Gf/* Haste.Ajax.POST */, _Hd/* Form.lvl16 */, new T2(1,new T2(0,_He/* Form.lvl17 */,new T(function(){
        return B(_1R/* GHC.Show.$fShowInt_$cshow */(_LA/* s4J6 */));
      })),new T2(1,new T2(0,_Hf/* Form.lvl18 */,new T(function(){
        return B(_1R/* GHC.Show.$fShowInt_$cshow */(_LC/* s4J8 */));
      })),_k/* GHC.Types.[] */)), _LF/* s4Kp */, _/* EXTERNAL */]);});
    }
  }
},
_LZ/* lvl20 */ = function(_M0/* s4Kq */, _M1/* s4Kr */, _/* EXTERNAL */){
  return new F(function(){return _Lw/* Form.$wlvl */(_M0/* s4Kq */, _/* EXTERNAL */);});
},
_M2/* lvl21 */ = new T2(0,_E9/* Form.lvl15 */,_LZ/* Form.lvl20 */),
_M3/* lvl22 */ = new T1(1,_M2/* Form.lvl21 */),
_M4/* lvl23 */ = new T3(0,_4y/* GHC.Base.Nothing */,_4y/* GHC.Base.Nothing */,_M3/* Form.lvl22 */),
_M5/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'desc-subpane\'>"));
}),
_M6/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_M7/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\'long-desc\'>"));
}),
_M8/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/hint-icon.png\' style=\'margin-right: 5px;\'>"));
}),
_M9/* lvl28 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_E4/* Config.Config.staticURL */, _M8/* Form.lvl27 */));
}),
_Ma/* lvl29 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img src=\'", _M9/* Form.lvl28 */));
}),
_Mb/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("textarea"));
}),
_Mc/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span/>"));
}),
_Md/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#form"));
}),
_Me/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input"));
}),
_Mf/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input:checked"));
}),
_Mg/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("select"));
}),
_Mh/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'main-pane\'>"));
}),
_Mi/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'form-subpane\'>"));
}),
_Mj/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/valid.png\'/>"));
}),
_Mk/* lvl8 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_E4/* Config.Config.staticURL */, _Mj/* Form.lvl7 */));
}),
_Ml/* lvl9 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'valid\' class=\'validity-flag\' src=\'", _Mk/* Form.lvl8 */));
}),
_Mm/* click1 */ = function(_Mn/* sjWY */, _/* EXTERNAL */){
  return new F(function(){return _4t/* FormEngine.JQuery.$wa5 */(E(_Mn/* sjWY */), _/* EXTERNAL */);});
},
_Mo/* selectTab1 */ = function(_Mp/* sgOI */, _Mq/* sgOJ */, _/* EXTERNAL */){
  var _Mr/* sgOO */ = new T(function(){
    return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(new T(function(){
      return B(_5P/* GHC.List.$w!! */(_Mq/* sgOJ */, E(_Mp/* sgOI */)));
    },1)));
  },1),
  _Ms/* sgOQ */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, _Mr/* sgOO */)), _/* EXTERNAL */));
  return new F(function(){return _Mm/* FormEngine.JQuery.click1 */(_Ms/* sgOQ */, _/* EXTERNAL */);});
},
_Mt/* generateForm1 */ = function(_Mu/* s4Kt */, _/* EXTERNAL */){
  var _Mv/* s4Kv */ = B(_2E/* FormEngine.JQuery.select1 */(_Md/* Form.lvl31 */, _/* EXTERNAL */)),
  _Mw/* s4KA */ = new T2(1,_4H/* Form.aboutTab */,_Mu/* s4Kt */),
  _Mx/* s4M9 */ = new T(function(){
    var _My/* s4M8 */ = function(_Mz/* s4KC */, _/* EXTERNAL */){
      var _MA/* s4KE */ = B(_2E/* FormEngine.JQuery.select1 */(_Mh/* Form.lvl5 */, _/* EXTERNAL */)),
      _MB/* s4KJ */ = B(_X/* FormEngine.JQuery.$wa3 */(_Mi/* Form.lvl6 */, E(_MA/* s4KE */), _/* EXTERNAL */)),
      _MC/* s4KO */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _MD/* s4KR */ = __app1/* EXTERNAL */(_MC/* s4KO */, E(_MB/* s4KJ */)),
      _ME/* s4KU */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _MF/* s4KX */ = __app1/* EXTERNAL */(_ME/* s4KU */, _MD/* s4KR */),
      _MG/* s4L2 */ = B(_DR/* FormEngine.FormElement.Rendering.foldElements1 */(B(_l/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_Mz/* s4KC */)), new T3(0,_Mu/* s4Kt */,_Ml/* Form.lvl9 */,_E6/* Form.lvl12 */), _M4/* Form.lvl23 */, _MF/* s4KX */, _/* EXTERNAL */)),
      _MH/* s4L7 */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _MI/* s4La */ = __app1/* EXTERNAL */(_MH/* s4L7 */, E(_MG/* s4L2 */)),
      _MJ/* s4Ld */ = B(_X/* FormEngine.JQuery.$wa3 */(_M5/* Form.lvl24 */, _MI/* s4La */, _/* EXTERNAL */)),
      _MK/* s4Lj */ = B(_C/* FormEngine.JQuery.$wa20 */(_M6/* Form.lvl25 */, new T(function(){
        return B(_4O/* FormEngine.FormElement.Identifiers.descSubpaneId */(_Mz/* s4KC */));
      },1), E(_MJ/* s4Ld */), _/* EXTERNAL */)),
      _ML/* s4Lp */ = __app1/* EXTERNAL */(_MC/* s4KO */, E(_MK/* s4Lj */)),
      _MM/* s4Lt */ = __app1/* EXTERNAL */(_ME/* s4KU */, _ML/* s4Lp */),
      _MN/* s4Lw */ = B(_X/* FormEngine.JQuery.$wa3 */(_M7/* Form.lvl26 */, _MM/* s4Lt */, _/* EXTERNAL */)),
      _MO/* s4LC */ = B(_C/* FormEngine.JQuery.$wa20 */(_M6/* Form.lvl25 */, new T(function(){
        return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_Mz/* s4KC */));
      },1), E(_MN/* s4Lw */), _/* EXTERNAL */)),
      _MP/* s4LI */ = __app1/* EXTERNAL */(_MC/* s4KO */, E(_MO/* s4LC */)),
      _MQ/* s4LM */ = __app1/* EXTERNAL */(_ME/* s4KU */, _MP/* s4LI */),
      _MR/* s4LP */ = B(_X/* FormEngine.JQuery.$wa3 */(_Ma/* Form.lvl29 */, _MQ/* s4LM */, _/* EXTERNAL */)),
      _MS/* s4LU */ = B(_X/* FormEngine.JQuery.$wa3 */(_Mc/* Form.lvl30 */, E(_MR/* s4LP */), _/* EXTERNAL */)),
      _MT/* s4M0 */ = __app1/* EXTERNAL */(_MH/* s4L7 */, E(_MS/* s4LU */));
      return new F(function(){return __app1/* EXTERNAL */(_MH/* s4L7 */, _MT/* s4M0 */);});
    };
    return B(_8G/* GHC.Base.map */(_My/* s4M8 */, _Mu/* s4Kt */));
  }),
  _MU/* s4Mb */ = B(_3f/* FormEngine.FormElement.Tabs.$wa */(_Mw/* s4KA */, new T2(1,_4J/* Form.aboutTabPaneJq1 */,_Mx/* s4M9 */), E(_Mv/* s4Kv */), _/* EXTERNAL */)),
  _MV/* s4Me */ = B(_Mo/* FormEngine.FormElement.Tabs.selectTab1 */(_4z/* Form.aboutTab4 */, _Mw/* s4KA */, _/* EXTERNAL */)),
  _MW/* s4Mh */ = B(_2E/* FormEngine.JQuery.select1 */(_Mf/* Form.lvl33 */, _/* EXTERNAL */)),
  _MX/* s4Mm */ = B(_4t/* FormEngine.JQuery.$wa5 */(E(_MW/* s4Mh */), _/* EXTERNAL */)),
  _MY/* s4Mr */ = B(_4t/* FormEngine.JQuery.$wa5 */(E(_MX/* s4Mm */), _/* EXTERNAL */)),
  _MZ/* s4Mu */ = B(_2E/* FormEngine.JQuery.select1 */(_Me/* Form.lvl32 */, _/* EXTERNAL */)),
  _N0/* s4Mz */ = B(_4o/* FormEngine.JQuery.$wa14 */(E(_MZ/* s4Mu */), _/* EXTERNAL */)),
  _N1/* s4MC */ = B(_2E/* FormEngine.JQuery.select1 */(_Mb/* Form.lvl3 */, _/* EXTERNAL */)),
  _N2/* s4MH */ = B(_4o/* FormEngine.JQuery.$wa14 */(E(_N1/* s4MC */), _/* EXTERNAL */)),
  _N3/* s4MK */ = B(_2E/* FormEngine.JQuery.select1 */(_Mg/* Form.lvl4 */, _/* EXTERNAL */)),
  _N4/* s4MP */ = B(_4o/* FormEngine.JQuery.$wa14 */(E(_N3/* s4MK */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_N5/* hideJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hidden"));
}),
_N6/* initOverlay2 */ = function(_N7/* s37B */, _/* EXTERNAL */){
  var _N8/* s37D */ = B(_L7/* FormEngine.JQuery.selectById1 */(_L5/* Overlay.overlayId */, _/* EXTERNAL */)),
  _N9/* s37I */ = B(_K/* FormEngine.JQuery.$wa2 */(_L1/* FormEngine.JQuery.hideJq3 */, _N5/* FormEngine.JQuery.hideJq2 */, E(_N8/* s37D */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_Na/* main2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Error generating tabs"));
}),
_Nb/* $wgo2 */ = function(_Nc/*  s4PG */, _Nd/*  s4PH */, _Ne/*  s4PI */){
  while(1){
    var _Nf/*  $wgo2 */ = B((function(_Ng/* s4PG */, _Nh/* s4PH */, _Ni/* s4PI */){
      var _Nj/* s4PJ */ = E(_Ng/* s4PG */);
      if(!_Nj/* s4PJ */._){
        return new T2(0,_Nh/* s4PH */,_Ni/* s4PI */);
      }else{
        var _Nk/* s4PK */ = _Nj/* s4PJ */.a,
        _Nl/* s4PV */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_Ni/* s4PI */, new T2(1,new T(function(){
            return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_Nh/* s4PH */, _Nk/* s4PK */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _Nc/*  s4PG */ = _Nj/* s4PJ */.b;
        _Nd/*  s4PH */ = new T(function(){
          return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_Nh/* s4PH */, _Nk/* s4PK */)).a);
        });
        _Ne/*  s4PI */ = _Nl/* s4PV */;
        return __continue/* EXTERNAL */;
      }
    })(_Nc/*  s4PG */, _Nd/*  s4PH */, _Ne/*  s4PI */));
    if(_Nf/*  $wgo2 */!=__continue/* EXTERNAL */){
      return _Nf/*  $wgo2 */;
    }
  }
},
_Nn/* $wgo3 */ = function(_No/*  s4PW */, _Np/*  s4PX */, _Nq/*  s4PY */){
  while(1){
    var _Nr/*  $wgo3 */ = B((function(_Ns/* s4PW */, _Nt/* s4PX */, _Nu/* s4PY */){
      var _Nv/* s4PZ */ = E(_Ns/* s4PW */);
      if(!_Nv/* s4PZ */._){
        return new T2(0,_Nt/* s4PX */,_Nu/* s4PY */);
      }else{
        var _Nw/* s4Q0 */ = _Nv/* s4PZ */.a,
        _Nx/* s4Qb */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_Nu/* s4PY */, new T2(1,new T(function(){
            return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_Nt/* s4PX */, _Nw/* s4Q0 */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _No/*  s4PW */ = _Nv/* s4PZ */.b;
        _Np/*  s4PX */ = new T(function(){
          return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_Nt/* s4PX */, _Nw/* s4Q0 */)).a);
        });
        _Nq/*  s4PY */ = _Nx/* s4Qb */;
        return __continue/* EXTERNAL */;
      }
    })(_No/*  s4PW */, _Np/*  s4PX */, _Nq/*  s4PY */));
    if(_Nr/*  $wgo3 */!=__continue/* EXTERNAL */){
      return _Nr/*  $wgo3 */;
    }
  }
},
_Ny/* $wgo4 */ = function(_Nz/*  s4Qc */, _NA/*  s4Qd */, _NB/*  s4Qe */){
  while(1){
    var _NC/*  $wgo4 */ = B((function(_ND/* s4Qc */, _NE/* s4Qd */, _NF/* s4Qe */){
      var _NG/* s4Qf */ = E(_ND/* s4Qc */);
      if(!_NG/* s4Qf */._){
        return new T2(0,_NE/* s4Qd */,_NF/* s4Qe */);
      }else{
        var _NH/* s4Qg */ = _NG/* s4Qf */.a,
        _NI/* s4Qr */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_NF/* s4Qe */, new T2(1,new T(function(){
            return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_NE/* s4Qd */, _NH/* s4Qg */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _Nz/*  s4Qc */ = _NG/* s4Qf */.b;
        _NA/*  s4Qd */ = new T(function(){
          return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_NE/* s4Qd */, _NH/* s4Qg */)).a);
        });
        _NB/*  s4Qe */ = _NI/* s4Qr */;
        return __continue/* EXTERNAL */;
      }
    })(_Nz/*  s4Qc */, _NA/*  s4Qd */, _NB/*  s4Qe */));
    if(_NC/*  $wgo4 */!=__continue/* EXTERNAL */){
      return _NC/*  $wgo4 */;
    }
  }
},
_NJ/* $wgo5 */ = function(_NK/*  s4Qs */, _NL/*  s4Qt */, _NM/*  s4Qu */){
  while(1){
    var _NN/*  $wgo5 */ = B((function(_NO/* s4Qs */, _NP/* s4Qt */, _NQ/* s4Qu */){
      var _NR/* s4Qv */ = E(_NO/* s4Qs */);
      if(!_NR/* s4Qv */._){
        return new T2(0,_NP/* s4Qt */,_NQ/* s4Qu */);
      }else{
        var _NS/* s4Qw */ = _NR/* s4Qv */.a,
        _NT/* s4QH */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_NQ/* s4Qu */, new T2(1,new T(function(){
            return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_NP/* s4Qt */, _NS/* s4Qw */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _NK/*  s4Qs */ = _NR/* s4Qv */.b;
        _NL/*  s4Qt */ = new T(function(){
          return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_NP/* s4Qt */, _NS/* s4Qw */)).a);
        });
        _NM/*  s4Qu */ = _NT/* s4QH */;
        return __continue/* EXTERNAL */;
      }
    })(_NK/*  s4Qs */, _NL/*  s4Qt */, _NM/*  s4Qu */));
    if(_NN/*  $wgo5 */!=__continue/* EXTERNAL */){
      return _NN/*  $wgo5 */;
    }
  }
},
_NU/* $wgo6 */ = function(_NV/*  s4QI */, _NW/*  s4QJ */, _NX/*  s4QK */){
  while(1){
    var _NY/*  $wgo6 */ = B((function(_NZ/* s4QI */, _O0/* s4QJ */, _O1/* s4QK */){
      var _O2/* s4QL */ = E(_NZ/* s4QI */);
      if(!_O2/* s4QL */._){
        return new T2(0,_O0/* s4QJ */,_O1/* s4QK */);
      }else{
        var _O3/* s4QM */ = _O2/* s4QL */.a,
        _O4/* s4QX */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_O1/* s4QK */, new T2(1,new T(function(){
            return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_O0/* s4QJ */, _O3/* s4QM */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _NV/*  s4QI */ = _O2/* s4QL */.b;
        _NW/*  s4QJ */ = new T(function(){
          return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_O0/* s4QJ */, _O3/* s4QM */)).a);
        });
        _NX/*  s4QK */ = _O4/* s4QX */;
        return __continue/* EXTERNAL */;
      }
    })(_NV/*  s4QI */, _NW/*  s4QJ */, _NX/*  s4QK */));
    if(_NY/*  $wgo6 */!=__continue/* EXTERNAL */){
      return _NY/*  $wgo6 */;
    }
  }
},
_O5/* xs */ = new T(function(){
  return new T2(1,_51/* FormEngine.FormItem.$fShowNumbering2 */,_O5/* FormEngine.FormItem.xs */);
}),
_O6/* incrementAtLevel */ = function(_O7/* s4Pj */){
  var _O8/* s4Pk */ = E(_O7/* s4Pj */);
  if(!_O8/* s4Pk */._){
    return __Z/* EXTERNAL */;
  }else{
    var _O9/* s4Pl */ = _O8/* s4Pk */.a,
    _Oa/* s4Pm */ = _O8/* s4Pk */.b,
    _Ob/* s4PF */ = new T(function(){
      var _Oc/* s4Pn */ = E(_Oa/* s4Pm */),
      _Od/* s4Pt */ = new T2(1,new T(function(){
        return B(_5P/* GHC.List.$w!! */(_O9/* s4Pl */, _Oc/* s4Pn */))+1|0;
      }),_O5/* FormEngine.FormItem.xs */);
      if(0>=_Oc/* s4Pn */){
        return E(_Od/* s4Pt */);
      }else{
        var _Oe/* s4Pw */ = function(_Of/* s4Px */, _Og/* s4Py */){
          var _Oh/* s4Pz */ = E(_Of/* s4Px */);
          if(!_Oh/* s4Pz */._){
            return E(_Od/* s4Pt */);
          }else{
            var _Oi/* s4PA */ = _Oh/* s4Pz */.a,
            _Oj/* s4PC */ = E(_Og/* s4Py */);
            return (_Oj/* s4PC */==1) ? new T2(1,_Oi/* s4PA */,_Od/* s4Pt */) : new T2(1,_Oi/* s4PA */,new T(function(){
              return B(_Oe/* s4Pw */(_Oh/* s4Pz */.b, _Oj/* s4PC */-1|0));
            }));
          }
        };
        return B(_Oe/* s4Pw */(_O9/* s4Pl */, _Oc/* s4Pn */));
      }
    });
    return new T2(1,_Ob/* s4PF */,_Oa/* s4Pm */);
  }
},
_Ok/* $wgo7 */ = function(_Ol/*  s4QY */, _Om/*  s4QZ */, _On/*  s4R0 */){
  while(1){
    var _Oo/*  $wgo7 */ = B((function(_Op/* s4QY */, _Oq/* s4QZ */, _Or/* s4R0 */){
      var _Os/* s4R1 */ = E(_Op/* s4QY */);
      if(!_Os/* s4R1 */._){
        return new T2(0,_Oq/* s4QZ */,_Or/* s4R0 */);
      }else{
        var _Ot/* s4R3 */ = _Os/* s4R1 */.b,
        _Ou/* s4R4 */ = E(_Os/* s4R1 */.a);
        if(!_Ou/* s4R4 */._){
          var _Ov/*   s4QZ */ = _Oq/* s4QZ */;
          _Ol/*  s4QY */ = _Ot/* s4R3 */;
          _Om/*  s4QZ */ = _Ov/*   s4QZ */;
          _On/*  s4R0 */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_Or/* s4R0 */, new T2(1,_Ou/* s4R4 */,_k/* GHC.Types.[] */)));
          });
          return __continue/* EXTERNAL */;
        }else{
          var _Ow/* s4Rq */ = new T(function(){
            var _Ox/* s4Rn */ = new T(function(){
              var _Oy/* s4Rj */ = new T(function(){
                var _Oz/* s4Rc */ = E(_Oq/* s4QZ */);
                if(!_Oz/* s4Rc */._){
                  return __Z/* EXTERNAL */;
                }else{
                  return new T2(1,_Oz/* s4Rc */.a,new T(function(){
                    return E(_Oz/* s4Rc */.b)+1|0;
                  }));
                }
              });
              return E(B(_NU/* FormEngine.FormItem.$wgo6 */(_Ou/* s4R4 */.c, _Oy/* s4Rj */, _k/* GHC.Types.[] */)).b);
            });
            return B(_7/* GHC.Base.++ */(_Or/* s4R0 */, new T2(1,new T3(1,_Oq/* s4QZ */,_Ou/* s4R4 */.b,_Ox/* s4Rn */),_k/* GHC.Types.[] */)));
          });
          _Ol/*  s4QY */ = _Ot/* s4R3 */;
          _Om/*  s4QZ */ = new T(function(){
            return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_Oq/* s4QZ */));
          });
          _On/*  s4R0 */ = _Ow/* s4Rq */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_Ol/*  s4QY */, _Om/*  s4QZ */, _On/*  s4R0 */));
    if(_Oo/*  $wgo7 */!=__continue/* EXTERNAL */){
      return _Oo/*  $wgo7 */;
    }
  }
},
_Nm/* $wincrementNumbering */ = function(_OA/* s4Rr */, _OB/* s4Rs */){
  var _OC/* s4Rt */ = E(_OB/* s4Rs */);
  switch(_OC/* s4Rt */._){
    case 0:
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T1(0,new T(function(){
        var _OD/* s4Rw */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OD/* s4Rw */.a,b:_OA/* s4Rr */,c:_OD/* s4Rw */.c,d:_OD/* s4Rw */.d,e:_OD/* s4Rw */.e,f:_OD/* s4Rw */.f,g:_OD/* s4Rw */.g,h:_OD/* s4Rw */.h,i:_OD/* s4Rw */.i,j:_OD/* s4Rw */.j,k:_OD/* s4Rw */.k};
      })));
    case 1:
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T1(1,new T(function(){
        var _OE/* s4RM */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OE/* s4RM */.a,b:_OA/* s4Rr */,c:_OE/* s4RM */.c,d:_OE/* s4RM */.d,e:_OE/* s4RM */.e,f:_OE/* s4RM */.f,g:_OE/* s4RM */.g,h:_OE/* s4RM */.h,i:_OE/* s4RM */.i,j:_OE/* s4RM */.j,k:_OE/* s4RM */.k};
      })));
    case 2:
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T1(2,new T(function(){
        var _OF/* s4S2 */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OF/* s4S2 */.a,b:_OA/* s4Rr */,c:_OF/* s4S2 */.c,d:_OF/* s4S2 */.d,e:_OF/* s4S2 */.e,f:_OF/* s4S2 */.f,g:_OF/* s4S2 */.g,h:_OF/* s4S2 */.h,i:_OF/* s4S2 */.i,j:_OF/* s4S2 */.j,k:_OF/* s4S2 */.k};
      })));
    case 3:
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T2(3,new T(function(){
        var _OG/* s4Sj */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OG/* s4Sj */.a,b:_OA/* s4Rr */,c:_OG/* s4Sj */.c,d:_OG/* s4Sj */.d,e:_OG/* s4Sj */.e,f:_OG/* s4Sj */.f,g:_OG/* s4Sj */.g,h:_OG/* s4Sj */.h,i:_OG/* s4Sj */.i,j:_OG/* s4Sj */.j,k:_OG/* s4Sj */.k};
      }),_OC/* s4Rt */.b));
    case 4:
      var _OH/* s4SY */ = new T(function(){
        var _OI/* s4SU */ = new T(function(){
          var _OJ/* s4SN */ = E(_OA/* s4Rr */);
          if(!_OJ/* s4SN */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_OJ/* s4SN */.a,new T(function(){
              return E(_OJ/* s4SN */.b)+1|0;
            }));
          }
        });
        return E(B(_Ok/* FormEngine.FormItem.$wgo7 */(_OC/* s4Rt */.b, _OI/* s4SU */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T2(4,new T(function(){
        var _OK/* s4SA */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OK/* s4SA */.a,b:_OA/* s4Rr */,c:_OK/* s4SA */.c,d:_OK/* s4SA */.d,e:_OK/* s4SA */.e,f:_OK/* s4SA */.f,g:_OK/* s4SA */.g,h:_OK/* s4SA */.h,i:_OK/* s4SA */.i,j:_OK/* s4SA */.j,k:_OK/* s4SA */.k};
      }),_OH/* s4SY */));
    case 5:
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T2(5,new T(function(){
        var _OL/* s4T3 */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OL/* s4T3 */.a,b:_OA/* s4Rr */,c:_OL/* s4T3 */.c,d:_OL/* s4T3 */.d,e:_OL/* s4T3 */.e,f:_OL/* s4T3 */.f,g:_OL/* s4T3 */.g,h:_OL/* s4T3 */.h,i:_OL/* s4T3 */.i,j:_OL/* s4T3 */.j,k:_OL/* s4T3 */.k};
      }),_OC/* s4Rt */.b));
    case 6:
      var _OM/* s4TI */ = new T(function(){
        var _ON/* s4TE */ = new T(function(){
          var _OO/* s4Tx */ = E(_OA/* s4Rr */);
          if(!_OO/* s4Tx */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_OO/* s4Tx */.a,new T(function(){
              return E(_OO/* s4Tx */.b)+1|0;
            }));
          }
        });
        return E(B(_NJ/* FormEngine.FormItem.$wgo5 */(_OC/* s4Rt */.b, _ON/* s4TE */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T2(6,new T(function(){
        var _OP/* s4Tk */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OP/* s4Tk */.a,b:_OA/* s4Rr */,c:_OP/* s4Tk */.c,d:_OP/* s4Tk */.d,e:_OP/* s4Tk */.e,f:_OP/* s4Tk */.f,g:_OP/* s4Tk */.g,h:_OP/* s4Tk */.h,i:_OP/* s4Tk */.i,j:_OP/* s4Tk */.j,k:_OP/* s4Tk */.k};
      }),_OM/* s4TI */));
    case 7:
      var _OQ/* s4Ug */ = new T(function(){
        var _OR/* s4Uc */ = new T(function(){
          var _OS/* s4U5 */ = E(_OA/* s4Rr */);
          if(!_OS/* s4U5 */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_OS/* s4U5 */.a,new T(function(){
              return E(_OS/* s4U5 */.b)+1|0;
            }));
          }
        });
        return E(B(_Ny/* FormEngine.FormItem.$wgo4 */(_OC/* s4Rt */.c, _OR/* s4Uc */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T3(7,new T(function(){
        var _OT/* s4TO */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OT/* s4TO */.a,b:_OA/* s4Rr */,c:_OT/* s4TO */.c,d:_OT/* s4TO */.d,e:_OT/* s4TO */.e,f:_OT/* s4TO */.f,g:_OT/* s4TO */.g,h:_OT/* s4TO */.h,i:_OT/* s4TO */.i,j:_OT/* s4TO */.j,k:_OT/* s4TO */.k};
      }),new T(function(){
        var _OU/* s4U1 */ = E(_OA/* s4Rr */);
        if(!_OU/* s4U1 */._){
          return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_OU/* s4U1 */.b);
        }
      }),_OQ/* s4Ug */));
    case 8:
      var _OV/* s4UO */ = new T(function(){
        var _OW/* s4UK */ = new T(function(){
          var _OX/* s4UD */ = E(_OA/* s4Rr */);
          if(!_OX/* s4UD */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_OX/* s4UD */.a,new T(function(){
              return E(_OX/* s4UD */.b)+1|0;
            }));
          }
        });
        return E(B(_Nn/* FormEngine.FormItem.$wgo3 */(_OC/* s4Rt */.c, _OW/* s4UK */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T3(8,new T(function(){
        var _OY/* s4Um */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_OY/* s4Um */.a,b:_OA/* s4Rr */,c:_OY/* s4Um */.c,d:_OY/* s4Um */.d,e:_OY/* s4Um */.e,f:_OY/* s4Um */.f,g:_OY/* s4Um */.g,h:_OY/* s4Um */.h,i:_OY/* s4Um */.i,j:_OY/* s4Um */.j,k:_OY/* s4Um */.k};
      }),new T(function(){
        var _OZ/* s4Uz */ = E(_OA/* s4Rr */);
        if(!_OZ/* s4Uz */._){
          return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_OZ/* s4Uz */.b);
        }
      }),_OV/* s4UO */));
    case 9:
      var _P0/* s4Vm */ = new T(function(){
        var _P1/* s4Vi */ = new T(function(){
          var _P2/* s4Vb */ = E(_OA/* s4Rr */);
          if(!_P2/* s4Vb */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_P2/* s4Vb */.a,new T(function(){
              return E(_P2/* s4Vb */.b)+1|0;
            }));
          }
        });
        return E(B(_Nb/* FormEngine.FormItem.$wgo2 */(_OC/* s4Rt */.c, _P1/* s4Vi */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_O6/* FormEngine.FormItem.incrementAtLevel */(_OA/* s4Rr */));
      }),new T3(9,new T(function(){
        var _P3/* s4UU */ = E(_OC/* s4Rt */.a);
        return {_:0,a:_P3/* s4UU */.a,b:_OA/* s4Rr */,c:_P3/* s4UU */.c,d:_P3/* s4UU */.d,e:_P3/* s4UU */.e,f:_P3/* s4UU */.f,g:_P3/* s4UU */.g,h:_P3/* s4UU */.h,i:_P3/* s4UU */.i,j:_P3/* s4UU */.j,k:_P3/* s4UU */.k};
      }),new T(function(){
        var _P4/* s4V7 */ = E(_OA/* s4Rr */);
        if(!_P4/* s4V7 */._){
          return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_P4/* s4V7 */.b);
        }
      }),_P0/* s4Vm */));
    case 10:
      return new T2(0,_OA/* s4Rr */,_OC/* s4Rt */);
    default:
      return new T2(0,_OA/* s4Rr */,_OC/* s4Rt */);
  }
},
_P5/* $wgo1 */ = function(_P6/*  s4Ya */, _P7/*  s4Yb */, _P8/*  s4Yc */){
  while(1){
    var _P9/*  $wgo1 */ = B((function(_Pa/* s4Ya */, _Pb/* s4Yb */, _Pc/* s4Yc */){
      var _Pd/* s4Yd */ = E(_Pa/* s4Ya */);
      if(!_Pd/* s4Yd */._){
        return new T2(0,_Pb/* s4Yb */,_Pc/* s4Yc */);
      }else{
        var _Pe/* s4Ye */ = _Pd/* s4Yd */.a,
        _Pf/* s4Yp */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_Pc/* s4Yc */, new T2(1,new T(function(){
            return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_Pb/* s4Yb */, _Pe/* s4Ye */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _P6/*  s4Ya */ = _Pd/* s4Yd */.b;
        _P7/*  s4Yb */ = new T(function(){
          return E(B(_Nm/* FormEngine.FormItem.$wincrementNumbering */(_Pb/* s4Yb */, _Pe/* s4Ye */)).a);
        });
        _P8/*  s4Yc */ = _Pf/* s4Yp */;
        return __continue/* EXTERNAL */;
      }
    })(_P6/*  s4Ya */, _P7/*  s4Yb */, _P8/*  s4Yc */));
    if(_P9/*  $wgo1 */!=__continue/* EXTERNAL */){
      return _P9/*  $wgo1 */;
    }
  }
},
_Pg/* formItems21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_Ph/* formItems20 */ = new T1(0,_Pg/* Questionnaire.formItems21 */),
_Pi/* formItems19 */ = new T2(1,_Ph/* Questionnaire.formItems20 */,_k/* GHC.Types.[] */),
_Pj/* formItems23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_Pk/* formItems22 */ = new T1(0,_Pj/* Questionnaire.formItems23 */),
_Pl/* formItems18 */ = new T2(1,_Pk/* Questionnaire.formItems22 */,_Pi/* Questionnaire.formItems19 */),
_Pm/* NoNumbering */ = __Z/* EXTERNAL */,
_Pn/* formItems26 */ = 6,
_Po/* formItems25 */ = new T1(1,_Pn/* Questionnaire.formItems26 */),
_Pp/* formItems288 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you require substantial amounts of compute power, amounts that are not trivially absorbed in what you usually have abailable, some planning is necessary. Do you think you need to do compute capacity planning?</p>"));
}),
_Pq/* formItems287 */ = new T1(1,_Pp/* Questionnaire.formItems288 */),
_Pr/* formItems290 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to do compute capacity planning?"));
}),
_Ps/* formItems289 */ = new T1(1,_Pr/* Questionnaire.formItems290 */),
_Pt/* formItems71 */ = 2,
_Pu/* formItems70 */ = new T1(1,_Pt/* Questionnaire.formItems71 */),
_Pv/* formItems286 */ = {_:0,a:_Ps/* Questionnaire.formItems289 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Pq/* Questionnaire.formItems287 */,g:_Pu/* Questionnaire.formItems70 */,h:_Po/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Pw/* formItems285 */ = new T2(4,_Pv/* Questionnaire.formItems286 */,_Pl/* Questionnaire.formItems18 */),
_Px/* formItems284 */ = new T2(1,_Pw/* Questionnaire.formItems285 */,_k/* GHC.Types.[] */),
_Py/* formItems291 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_Po/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Pz/* formItems31 */ = 0,
_PA/* formItems283 */ = new T3(7,_Py/* Questionnaire.formItems291 */,_Pz/* Questionnaire.formItems31 */,_Px/* Questionnaire.formItems284 */),
_PB/* formItems282 */ = new T2(1,_PA/* Questionnaire.formItems283 */,_k/* GHC.Types.[] */),
_PC/* formItems115 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Drill deeper"));
}),
_PD/* formItems114 */ = new T1(0,_PC/* Questionnaire.formItems115 */),
_PE/* formItems113 */ = new T2(1,_PD/* Questionnaire.formItems114 */,_k/* GHC.Types.[] */),
_PF/* formItems295 */ = new T2(1,_Ph/* Questionnaire.formItems20 */,_PE/* Questionnaire.formItems113 */),
_PG/* formItems298 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">There are many factors that can contribute to the risk of information loss or information theft. They are often part of the behavior of the people that are involved in the project, but can also be steered by properly planned infrastructure.</p>"));
}),
_PH/* formItems297 */ = new T1(1,_PG/* Questionnaire.formItems298 */),
_PI/* formItems300 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the risk of information loss or theft acceptable?"));
}),
_PJ/* formItems299 */ = new T1(1,_PI/* Questionnaire.formItems300 */),
_PK/* formItems44 */ = 5,
_PL/* formItems43 */ = new T1(1,_PK/* Questionnaire.formItems44 */),
_PM/* formItems296 */ = {_:0,a:_PJ/* Questionnaire.formItems299 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_PH/* Questionnaire.formItems297 */,g:_Pu/* Questionnaire.formItems70 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_PN/* formItems294 */ = new T2(4,_PM/* Questionnaire.formItems296 */,_PF/* Questionnaire.formItems295 */),
_PO/* formItems293 */ = new T2(1,_PN/* Questionnaire.formItems294 */,_k/* GHC.Types.[] */),
_PP/* formItems301 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_PQ/* formItems292 */ = new T3(7,_PP/* Questionnaire.formItems301 */,_Pz/* Questionnaire.formItems31 */,_PO/* Questionnaire.formItems293 */),
_PR/* formItems281 */ = new T2(1,_PQ/* Questionnaire.formItems292 */,_PB/* Questionnaire.formItems282 */),
_PS/* formItems307 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you collect substantial amounts of data, amounts that do not trivially fit on the storage that you normally have available or that can not be trivially transported between systems, some planning is necessary. Do you think you need to do storage capacity planning? If the expected total data volume is larger than 1 TB, you probably need to answer \'yes\' here.</p>"));
}),
_PT/* formItems306 */ = new T1(1,_PS/* Questionnaire.formItems307 */),
_PU/* formItems309 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to do storage capacity planning?"));
}),
_PV/* formItems308 */ = new T1(1,_PU/* Questionnaire.formItems309 */),
_PW/* formItems53 */ = 4,
_PX/* formItems52 */ = new T1(1,_PW/* Questionnaire.formItems53 */),
_PY/* formItems305 */ = {_:0,a:_PV/* Questionnaire.formItems308 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_PT/* Questionnaire.formItems306 */,g:_Pu/* Questionnaire.formItems70 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_PZ/* formItems304 */ = new T2(4,_PY/* Questionnaire.formItems305 */,_Pl/* Questionnaire.formItems18 */),
_Q0/* formItems303 */ = new T2(1,_PZ/* Questionnaire.formItems304 */,_k/* GHC.Types.[] */),
_Q1/* formItems310 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Q2/* formItems302 */ = new T3(7,_Q1/* Questionnaire.formItems310 */,_Pz/* Questionnaire.formItems31 */,_Q0/* Questionnaire.formItems303 */),
_Q3/* formItems280 */ = new T2(1,_Q2/* Questionnaire.formItems302 */,_PR/* Questionnaire.formItems281 */),
_Q4/* formItems317 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Explore"));
}),
_Q5/* formItems316 */ = new T1(0,_Q4/* Questionnaire.formItems317 */),
_Q6/* formItems315 */ = new T2(1,_Q5/* Questionnaire.formItems316 */,_k/* GHC.Types.[] */),
_Q7/* formItems41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Skip"));
}),
_Q8/* formItems40 */ = new T1(0,_Q7/* Questionnaire.formItems41 */),
_Q9/* formItems314 */ = new T2(1,_Q8/* Questionnaire.formItems40 */,_Q6/* Questionnaire.formItems315 */),
_Qa/* formItems320 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">For the re-usability of your data by yourself or others at a later stage, a lot of information about the data, how it was collected and how it can be used should be stored with the data. Such data about the data is called metadata, and this set of questions are about this metadata</p>"));
}),
_Qb/* formItems319 */ = new T1(1,_Qa/* Questionnaire.formItems320 */),
_Qc/* formItems322 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you be storing metadata?"));
}),
_Qd/* formItems321 */ = new T1(1,_Qc/* Questionnaire.formItems322 */),
_Qe/* formItems62 */ = 3,
_Qf/* formItems61 */ = new T1(1,_Qe/* Questionnaire.formItems62 */),
_Qg/* formItems318 */ = {_:0,a:_Qd/* Questionnaire.formItems321 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Qb/* Questionnaire.formItems319 */,g:_Pu/* Questionnaire.formItems70 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qh/* formItems313 */ = new T2(4,_Qg/* Questionnaire.formItems318 */,_Q9/* Questionnaire.formItems314 */),
_Qi/* formItems312 */ = new T2(1,_Qh/* Questionnaire.formItems313 */,_k/* GHC.Types.[] */),
_Qj/* formItems323 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qk/* formItems311 */ = new T3(7,_Qj/* Questionnaire.formItems323 */,_Pz/* Questionnaire.formItems31 */,_Qi/* Questionnaire.formItems312 */),
_Ql/* formItems279 */ = new T2(1,_Qk/* Questionnaire.formItems311 */,_Q3/* Questionnaire.formItems280 */),
_Qm/* formItems329 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using new types of data?"));
}),
_Qn/* formItems328 */ = new T1(1,_Qm/* Questionnaire.formItems329 */),
_Qo/* formItems327 */ = {_:0,a:_Qn/* Questionnaire.formItems328 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qp/* formItems326 */ = new T2(4,_Qo/* Questionnaire.formItems327 */,_Pl/* Questionnaire.formItems18 */),
_Qq/* formItems325 */ = new T2(1,_Qp/* Questionnaire.formItems326 */,_k/* GHC.Types.[] */),
_Qr/* formItems330 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qs/* formItems324 */ = new T3(7,_Qr/* Questionnaire.formItems330 */,_Pz/* Questionnaire.formItems31 */,_Qq/* Questionnaire.formItems325 */),
_Qt/* formItems278 */ = new T2(1,_Qs/* Questionnaire.formItems324 */,_Ql/* Questionnaire.formItems279 */),
_Qu/* formItems336 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Are you using data types used by others too?"));
}),
_Qv/* formItems335 */ = new T1(1,_Qu/* Questionnaire.formItems336 */),
_Qw/* formItems80 */ = 1,
_Qx/* formItems79 */ = new T1(1,_Qw/* Questionnaire.formItems80 */),
_Qy/* formItems334 */ = {_:0,a:_Qv/* Questionnaire.formItems335 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qz/* formItems333 */ = new T2(4,_Qy/* Questionnaire.formItems334 */,_Pl/* Questionnaire.formItems18 */),
_QA/* formItems332 */ = new T2(1,_Qz/* Questionnaire.formItems333 */,_k/* GHC.Types.[] */),
_QB/* formItems337 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Pu/* Questionnaire.formItems70 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QC/* formItems331 */ = new T3(7,_QB/* Questionnaire.formItems337 */,_Pz/* Questionnaire.formItems31 */,_QA/* Questionnaire.formItems332 */),
_QD/* formItems277 */ = new T2(1,_QC/* Questionnaire.formItems331 */,_Qt/* Questionnaire.formItems278 */),
_QE/* formItems340 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("In the data design and planning phase, we will make sure that we know what data comes when, that we have enough storage space and compute power to deal with it, and that all the responsibilities have been taken care of."));
}),
_QF/* formItems339 */ = new T1(1,_QE/* Questionnaire.formItems340 */),
_QG/* formItems342 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data design and planning"));
}),
_QH/* formItems341 */ = new T1(1,_QG/* Questionnaire.formItems342 */),
_QI/* formItems86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("chapter"));
}),
_QJ/* formItems85 */ = new T1(1,_QI/* Questionnaire.formItems86 */),
_QK/* formItems338 */ = {_:0,a:_QH/* Questionnaire.formItems341 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_QF/* Questionnaire.formItems339 */,g:_Pu/* Questionnaire.formItems70 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_QL/* formItems276 */ = new T2(6,_QK/* Questionnaire.formItems338 */,_QD/* Questionnaire.formItems277 */),
_QM/* formItems240 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is there a data integration tool that can handle and combine all the data types you are dealing with in your project?"));
}),
_QN/* formItems239 */ = new T1(1,_QM/* Questionnaire.formItems240 */),
_QO/* formItems238 */ = {_:0,a:_QN/* Questionnaire.formItems239 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QP/* formItems237 */ = new T2(4,_QO/* Questionnaire.formItems238 */,_Pl/* Questionnaire.formItems18 */),
_QQ/* formItems236 */ = new T2(1,_QP/* Questionnaire.formItems237 */,_k/* GHC.Types.[] */),
_QR/* formItems241 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QS/* formItems235 */ = new T3(7,_QR/* Questionnaire.formItems241 */,_Pz/* Questionnaire.formItems31 */,_QQ/* Questionnaire.formItems236 */),
_QT/* formItems234 */ = new T2(1,_QS/* Questionnaire.formItems235 */,_k/* GHC.Types.[] */),
_QU/* formItems247 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you have any non-equipment data capture?"));
}),
_QV/* formItems246 */ = new T1(1,_QU/* Questionnaire.formItems247 */),
_QW/* formItems245 */ = {_:0,a:_QV/* Questionnaire.formItems246 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QX/* formItems244 */ = new T2(4,_QW/* Questionnaire.formItems245 */,_Pl/* Questionnaire.formItems18 */),
_QY/* formItems243 */ = new T2(1,_QX/* Questionnaire.formItems244 */,_k/* GHC.Types.[] */),
_QZ/* formItems248 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_R0/* formItems242 */ = new T3(7,_QZ/* Questionnaire.formItems248 */,_Pz/* Questionnaire.formItems31 */,_QY/* Questionnaire.formItems243 */),
_R1/* formItems233 */ = new T2(1,_R0/* Questionnaire.formItems242 */,_QT/* Questionnaire.formItems234 */),
_R2/* formItems254 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Where does the data come from? And who will need it? Sometimes the raw data is measured somewhere else than where the primary processing is taking place. In such cases the ingestion of the primary data may take special planning.</p>"));
}),
_R3/* formItems253 */ = new T1(1,_R2/* Questionnaire.formItems254 */),
_R4/* formItems256 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is special care needed to get the raw data ready for processing?"));
}),
_R5/* formItems255 */ = new T1(1,_R4/* Questionnaire.formItems256 */),
_R6/* formItems252 */ = {_:0,a:_R5/* Questionnaire.formItems255 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_R3/* Questionnaire.formItems253 */,g:_Qf/* Questionnaire.formItems61 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_R7/* formItems251 */ = new T2(4,_R6/* Questionnaire.formItems252 */,_Pl/* Questionnaire.formItems18 */),
_R8/* formItems250 */ = new T2(1,_R7/* Questionnaire.formItems251 */,_k/* GHC.Types.[] */),
_R9/* formItems257 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ra/* formItems249 */ = new T3(7,_R9/* Questionnaire.formItems257 */,_Pz/* Questionnaire.formItems31 */,_R8/* Questionnaire.formItems250 */),
_Rb/* formItems232 */ = new T2(1,_Ra/* Questionnaire.formItems249 */,_R1/* Questionnaire.formItems233 */),
_Rc/* formItems264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External party"));
}),
_Rd/* formItems263 */ = new T1(0,_Rc/* Questionnaire.formItems264 */),
_Re/* formItems262 */ = new T2(1,_Rd/* Questionnaire.formItems263 */,_k/* GHC.Types.[] */),
_Rf/* formItems266 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("In the project"));
}),
_Rg/* formItems265 */ = new T1(0,_Rf/* Questionnaire.formItems266 */),
_Rh/* formItems261 */ = new T2(1,_Rg/* Questionnaire.formItems265 */,_Re/* Questionnaire.formItems262 */),
_Ri/* formItems269 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Are there easily accessible specialized service providers for data capture?</p>"));
}),
_Rj/* formItems268 */ = new T1(1,_Ri/* Questionnaire.formItems269 */),
_Rk/* formItems271 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Who will do the measurements?"));
}),
_Rl/* formItems270 */ = new T1(1,_Rk/* Questionnaire.formItems271 */),
_Rm/* formItems267 */ = {_:0,a:_Rl/* Questionnaire.formItems270 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Rj/* Questionnaire.formItems268 */,g:_Qf/* Questionnaire.formItems61 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Rn/* formItems260 */ = new T2(4,_Rm/* Questionnaire.formItems267 */,_Rh/* Questionnaire.formItems261 */),
_Ro/* formItems259 */ = new T2(1,_Rn/* Questionnaire.formItems260 */,_k/* GHC.Types.[] */),
_Rp/* formItems272 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Rq/* formItems258 */ = new T3(7,_Rp/* Questionnaire.formItems272 */,_Pz/* Questionnaire.formItems31 */,_Ro/* Questionnaire.formItems259 */),
_Rr/* formItems231 */ = new T2(1,_Rq/* Questionnaire.formItems258 */,_Rb/* Questionnaire.formItems232 */),
_Rs/* formItems275 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data Capture (the equipment phase)"));
}),
_Rt/* formItems274 */ = new T1(1,_Rs/* Questionnaire.formItems275 */),
_Ru/* formItems273 */ = {_:0,a:_Rt/* Questionnaire.formItems274 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_4y/* GHC.Base.Nothing */,g:_Qf/* Questionnaire.formItems61 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_Rv/* formItems230 */ = new T2(6,_Ru/* Questionnaire.formItems273 */,_Rr/* Questionnaire.formItems231 */),
_Rw/* formItems195 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We have an alternative"));
}),
_Rx/* formItems194 */ = new T1(0,_Rw/* Questionnaire.formItems195 */),
_Ry/* formItems193 */ = new T2(1,_Rx/* Questionnaire.formItems194 */,_k/* GHC.Types.[] */),
_Rz/* formItems197 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Wait"));
}),
_RA/* formItems196 */ = new T1(0,_Rz/* Questionnaire.formItems197 */),
_RB/* formItems192 */ = new T2(1,_RA/* Questionnaire.formItems196 */,_Ry/* Questionnaire.formItems193 */),
_RC/* formItems200 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">What will you do if the compute facility is down?</p>"));
}),
_RD/* formItems199 */ = new T1(1,_RC/* Questionnaire.formItems200 */),
_RE/* formItems202 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you have a contingency plan?"));
}),
_RF/* formItems201 */ = new T1(1,_RE/* Questionnaire.formItems202 */),
_RG/* formItems198 */ = {_:0,a:_RF/* Questionnaire.formItems201 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_RD/* Questionnaire.formItems199 */,g:_PX/* Questionnaire.formItems52 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RH/* formItems191 */ = new T2(4,_RG/* Questionnaire.formItems198 */,_RB/* Questionnaire.formItems192 */),
_RI/* formItems190 */ = new T2(1,_RH/* Questionnaire.formItems191 */,_k/* GHC.Types.[] */),
_RJ/* formItems203 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RK/* formItems189 */ = new T3(7,_RJ/* Questionnaire.formItems203 */,_Pz/* Questionnaire.formItems31 */,_RI/* Questionnaire.formItems190 */),
_RL/* formItems188 */ = new T2(1,_RK/* Questionnaire.formItems189 */,_k/* GHC.Types.[] */),
_RM/* formItems117 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Taken care of"));
}),
_RN/* formItems116 */ = new T1(0,_RM/* Questionnaire.formItems117 */),
_RO/* formItems112 */ = new T2(1,_RN/* Questionnaire.formItems116 */,_PE/* Questionnaire.formItems113 */),
_RP/* formItems209 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you validate the integrity of the results?"));
}),
_RQ/* formItems208 */ = new T1(1,_RP/* Questionnaire.formItems209 */),
_RR/* formItems207 */ = {_:0,a:_RQ/* Questionnaire.formItems208 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RS/* formItems206 */ = new T2(4,_RR/* Questionnaire.formItems207 */,_RO/* Questionnaire.formItems112 */),
_RT/* formItems205 */ = new T2(1,_RS/* Questionnaire.formItems206 */,_k/* GHC.Types.[] */),
_RU/* formItems210 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RV/* formItems204 */ = new T3(7,_RU/* Questionnaire.formItems210 */,_Pz/* Questionnaire.formItems31 */,_RT/* Questionnaire.formItems205 */),
_RW/* formItems187 */ = new T2(1,_RV/* Questionnaire.formItems204 */,_RL/* Questionnaire.formItems188 */),
_RX/* formItems216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you make sure to know what exactly has been run?"));
}),
_RY/* formItems215 */ = new T1(1,_RX/* Questionnaire.formItems216 */),
_RZ/* formItems214 */ = {_:0,a:_RY/* Questionnaire.formItems215 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_S0/* formItems213 */ = new T2(4,_RZ/* Questionnaire.formItems214 */,_RO/* Questionnaire.formItems112 */),
_S1/* formItems212 */ = new T2(1,_S0/* Questionnaire.formItems213 */,_k/* GHC.Types.[] */),
_S2/* formItems217 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_S3/* formItems211 */ = new T3(7,_S2/* Questionnaire.formItems217 */,_Pz/* Questionnaire.formItems31 */,_S1/* Questionnaire.formItems212 */),
_S4/* formItems186 */ = new T2(1,_S3/* Questionnaire.formItems211 */,_RW/* Questionnaire.formItems187 */),
_S5/* formItems223 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">It is likely that you will be developing or modifying the workflow for data processing. There are a lot of aspects of this workflow that can play a role in your data management, such as the use of an existing work flow engine, the use of existing software vs development of new components, and whether every run needs human intervention or whether all data processing can be run in bulk once the work flow has been defined.</p>"));
}),
_S6/* formItems222 */ = new T1(1,_S5/* Questionnaire.formItems223 */),
_S7/* formItems225 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Workflow development"));
}),
_S8/* formItems224 */ = new T1(1,_S7/* Questionnaire.formItems225 */),
_S9/* formItems221 */ = {_:0,a:_S8/* Questionnaire.formItems224 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_S6/* Questionnaire.formItems222 */,g:_PX/* Questionnaire.formItems52 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sa/* formItems220 */ = new T2(4,_S9/* Questionnaire.formItems221 */,_RO/* Questionnaire.formItems112 */),
_Sb/* formItems219 */ = new T2(1,_Sa/* Questionnaire.formItems220 */,_k/* GHC.Types.[] */),
_Sc/* formItems226 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sd/* formItems218 */ = new T3(7,_Sc/* Questionnaire.formItems226 */,_Pz/* Questionnaire.formItems31 */,_Sb/* Questionnaire.formItems219 */),
_Se/* formItems185 */ = new T2(1,_Sd/* Questionnaire.formItems218 */,_S4/* Questionnaire.formItems186 */),
_Sf/* formItems229 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data processing and curation"));
}),
_Sg/* formItems228 */ = new T1(1,_Sf/* Questionnaire.formItems229 */),
_Sh/* formItems227 */ = {_:0,a:_Sg/* Questionnaire.formItems228 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_4y/* GHC.Base.Nothing */,g:_PX/* Questionnaire.formItems52 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_Si/* formItems184 */ = new T2(6,_Sh/* Questionnaire.formItems227 */,_Se/* Questionnaire.formItems185 */),
_Sj/* formItems153 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you have all tools to couple the necessary data types?"));
}),
_Sk/* formItems152 */ = new T1(1,_Sj/* Questionnaire.formItems153 */),
_Sl/* formItems151 */ = {_:0,a:_Sk/* Questionnaire.formItems152 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sm/* formItems150 */ = new T2(4,_Sl/* Questionnaire.formItems151 */,_Pl/* Questionnaire.formItems18 */),
_Sn/* formItems149 */ = new T2(1,_Sm/* Questionnaire.formItems150 */,_k/* GHC.Types.[] */),
_So/* formItems154 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sp/* formItems148 */ = new T3(7,_So/* Questionnaire.formItems154 */,_Pz/* Questionnaire.formItems31 */,_Sn/* Questionnaire.formItems149 */),
_Sq/* formItems147 */ = new T2(1,_Sp/* Questionnaire.formItems148 */,_k/* GHC.Types.[] */),
_Sr/* formItems160 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will there be potential issues with statistical normalization?"));
}),
_Ss/* formItems159 */ = new T1(1,_Sr/* Questionnaire.formItems160 */),
_St/* formItems158 */ = {_:0,a:_Ss/* Questionnaire.formItems159 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Su/* formItems157 */ = new T2(4,_St/* Questionnaire.formItems158 */,_Pl/* Questionnaire.formItems18 */),
_Sv/* formItems156 */ = new T2(1,_Su/* Questionnaire.formItems157 */,_k/* GHC.Types.[] */),
_Sw/* formItems161 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sx/* formItems155 */ = new T3(7,_Sw/* Questionnaire.formItems161 */,_Pz/* Questionnaire.formItems31 */,_Sv/* Questionnaire.formItems156 */),
_Sy/* formItems146 */ = new T2(1,_Sx/* Questionnaire.formItems155 */,_Sq/* Questionnaire.formItems147 */),
_Sz/* formItems167 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using common ontologies?"));
}),
_SA/* formItems166 */ = new T1(1,_Sz/* Questionnaire.formItems167 */),
_SB/* formItems165 */ = {_:0,a:_SA/* Questionnaire.formItems166 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SC/* formItems164 */ = new T2(4,_SB/* Questionnaire.formItems165 */,_Pl/* Questionnaire.formItems18 */),
_SD/* formItems163 */ = new T2(1,_SC/* Questionnaire.formItems164 */,_k/* GHC.Types.[] */),
_SE/* formItems168 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SF/* formItems162 */ = new T3(7,_SE/* Questionnaire.formItems168 */,_Pz/* Questionnaire.formItems31 */,_SD/* Questionnaire.formItems163 */),
_SG/* formItems145 */ = new T2(1,_SF/* Questionnaire.formItems162 */,_Sy/* Questionnaire.formItems146 */),
_SH/* formItems174 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using common or exchangeable units?"));
}),
_SI/* formItems173 */ = new T1(1,_SH/* Questionnaire.formItems174 */),
_SJ/* formItems172 */ = {_:0,a:_SI/* Questionnaire.formItems173 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SK/* formItems171 */ = new T2(4,_SJ/* Questionnaire.formItems172 */,_Pl/* Questionnaire.formItems18 */),
_SL/* formItems170 */ = new T2(1,_SK/* Questionnaire.formItems171 */,_k/* GHC.Types.[] */),
_SM/* formItems175 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SN/* formItems169 */ = new T3(7,_SM/* Questionnaire.formItems175 */,_Pz/* Questionnaire.formItems31 */,_SL/* Questionnaire.formItems170 */),
_SO/* formItems144 */ = new T2(1,_SN/* Questionnaire.formItems169 */,_SG/* Questionnaire.formItems145 */),
_SP/* formItems181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What is the framework you will use for data integration?"));
}),
_SQ/* formItems180 */ = new T1(1,_SP/* Questionnaire.formItems181 */),
_SR/* formItems179 */ = {_:0,a:_SQ/* Questionnaire.formItems180 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SS/* formItems178 */ = new T2(4,_SR/* Questionnaire.formItems179 */,_RO/* Questionnaire.formItems112 */),
_ST/* formItems177 */ = new T2(1,_SS/* Questionnaire.formItems178 */,_k/* GHC.Types.[] */),
_SU/* formItems182 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SV/* formItems176 */ = new T3(7,_SU/* Questionnaire.formItems182 */,_Pz/* Questionnaire.formItems31 */,_ST/* Questionnaire.formItems177 */),
_SW/* formItems143 */ = new T2(1,_SV/* Questionnaire.formItems176 */,_SO/* Questionnaire.formItems144 */),
_SX/* formItems141 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data integration"));
}),
_SY/* formItems140 */ = new T1(1,_SX/* Questionnaire.formItems141 */),
_SZ/* formItems183 */ = {_:0,a:_SY/* Questionnaire.formItems140 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_4y/* GHC.Base.Nothing */,g:_PL/* Questionnaire.formItems43 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_T0/* formItems142 */ = new T2(6,_SZ/* Questionnaire.formItems183 */,_SW/* Questionnaire.formItems143 */),
_T1/* formItems28 */ = 7,
_T2/* formItems27 */ = new T1(1,_T1/* Questionnaire.formItems28 */),
_T3/* formItems88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Information and insight"));
}),
_T4/* formItems87 */ = new T1(1,_T3/* Questionnaire.formItems88 */),
_T5/* formItems84 */ = {_:0,a:_T4/* Questionnaire.formItems87 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_T6/* formItems30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be archiving data?"));
}),
_T7/* formItems29 */ = new T1(1,_T6/* Questionnaire.formItems30 */),
_T8/* formItems24 */ = {_:0,a:_T7/* Questionnaire.formItems29 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Po/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_T9/* formItems17 */ = new T2(4,_T8/* Questionnaire.formItems24 */,_Pl/* Questionnaire.formItems18 */),
_Ta/* formItems16 */ = new T2(1,_T9/* Questionnaire.formItems17 */,_k/* GHC.Types.[] */),
_Tb/* formItems32 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Po/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Tc/* formItems15 */ = new T3(7,_Tb/* Questionnaire.formItems32 */,_Pz/* Questionnaire.formItems31 */,_Ta/* Questionnaire.formItems16 */),
_Td/* formItems14 */ = new T2(1,_Tc/* Questionnaire.formItems15 */,_k/* GHC.Types.[] */),
_Te/* formItems39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Drill Deeper"));
}),
_Tf/* formItems38 */ = new T1(0,_Te/* Questionnaire.formItems39 */),
_Tg/* formItems37 */ = new T2(1,_Tf/* Questionnaire.formItems38 */,_k/* GHC.Types.[] */),
_Th/* formItems36 */ = new T2(1,_Q8/* Questionnaire.formItems40 */,_Tg/* Questionnaire.formItems37 */),
_Ti/* formItems46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you work out the financial aspects of making the data available?"));
}),
_Tj/* formItems45 */ = new T1(1,_Ti/* Questionnaire.formItems46 */),
_Tk/* formItems42 */ = {_:0,a:_Tj/* Questionnaire.formItems45 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Tl/* formItems35 */ = new T2(4,_Tk/* Questionnaire.formItems42 */,_Th/* Questionnaire.formItems36 */),
_Tm/* formItems34 */ = new T2(1,_Tl/* Questionnaire.formItems35 */,_k/* GHC.Types.[] */),
_Tn/* formItems47 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_To/* formItems33 */ = new T3(7,_Tn/* Questionnaire.formItems47 */,_Pz/* Questionnaire.formItems31 */,_Tm/* Questionnaire.formItems34 */),
_Tp/* formItems13 */ = new T2(1,_To/* Questionnaire.formItems33 */,_Td/* Questionnaire.formItems14 */),
_Tq/* formItems55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Where will you make your data available?"));
}),
_Tr/* formItems54 */ = new T1(1,_Tq/* Questionnaire.formItems55 */),
_Ts/* formItems51 */ = {_:0,a:_Tr/* Questionnaire.formItems54 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Tt/* formItems50 */ = new T2(4,_Ts/* Questionnaire.formItems51 */,_Th/* Questionnaire.formItems36 */),
_Tu/* formItems49 */ = new T2(1,_Tt/* Questionnaire.formItems50 */,_k/* GHC.Types.[] */),
_Tv/* formItems56 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Tw/* formItems48 */ = new T3(7,_Tv/* Questionnaire.formItems56 */,_Pz/* Questionnaire.formItems31 */,_Tu/* Questionnaire.formItems49 */),
_Tx/* formItems12 */ = new T2(1,_Tw/* Questionnaire.formItems48 */,_Tp/* Questionnaire.formItems13 */),
_Ty/* formItems64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" Are there business reasons why (some of your) data can not be completely open?"));
}),
_Tz/* formItems63 */ = new T1(1,_Ty/* Questionnaire.formItems64 */),
_TA/* formItems60 */ = {_:0,a:_Tz/* Questionnaire.formItems63 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TB/* formItems59 */ = new T2(4,_TA/* Questionnaire.formItems60 */,_Pl/* Questionnaire.formItems18 */),
_TC/* formItems58 */ = new T2(1,_TB/* Questionnaire.formItems59 */,_k/* GHC.Types.[] */),
_TD/* formItems65 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TE/* formItems57 */ = new T3(7,_TD/* Questionnaire.formItems65 */,_Pz/* Questionnaire.formItems31 */,_TC/* Questionnaire.formItems58 */),
_TF/* formItems11 */ = new T2(1,_TE/* Questionnaire.formItems57 */,_Tx/* Questionnaire.formItems12 */),
_TG/* formItems73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" Are there legal reasons why (some of your) data can not be completely open?"));
}),
_TH/* formItems72 */ = new T1(1,_TG/* Questionnaire.formItems73 */),
_TI/* formItems69 */ = {_:0,a:_TH/* Questionnaire.formItems72 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TJ/* formItems68 */ = new T2(4,_TI/* Questionnaire.formItems69 */,_Pl/* Questionnaire.formItems18 */),
_TK/* formItems67 */ = new T2(1,_TJ/* Questionnaire.formItems68 */,_k/* GHC.Types.[] */),
_TL/* formItems74 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TM/* formItems66 */ = new T3(7,_TL/* Questionnaire.formItems74 */,_Pz/* Questionnaire.formItems31 */,_TK/* Questionnaire.formItems67 */),
_TN/* formItems10 */ = new T2(1,_TM/* Questionnaire.formItems66 */,_TF/* Questionnaire.formItems11 */),
_TO/* formItems82 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be working with the philosophy \'as open as possible\' for your data?"));
}),
_TP/* formItems81 */ = new T1(1,_TO/* Questionnaire.formItems82 */),
_TQ/* formItems78 */ = {_:0,a:_TP/* Questionnaire.formItems81 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TR/* formItems77 */ = new T2(4,_TQ/* Questionnaire.formItems78 */,_Pl/* Questionnaire.formItems18 */),
_TS/* formItems76 */ = new T2(1,_TR/* Questionnaire.formItems77 */,_k/* GHC.Types.[] */),
_TT/* formItems83 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_T2/* Questionnaire.formItems27 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TU/* formItems75 */ = new T3(7,_TT/* Questionnaire.formItems83 */,_Pz/* Questionnaire.formItems31 */,_TS/* Questionnaire.formItems76 */),
_TV/* formItems9 */ = new T2(1,_TU/* Questionnaire.formItems75 */,_TN/* Questionnaire.formItems10 */),
_TW/* formItems8 */ = new T2(6,_T5/* Questionnaire.formItems84 */,_TV/* Questionnaire.formItems9 */),
_TX/* formItems7 */ = new T2(1,_TW/* Questionnaire.formItems8 */,_k/* GHC.Types.[] */),
_TY/* formItems139 */ = {_:0,a:_SY/* Questionnaire.formItems140 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_TZ/* formItems134 */ = new T2(1,_RN/* Questionnaire.formItems116 */,_Pi/* Questionnaire.formItems19 */),
_U0/* formItems137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will data interpretation and modeling require significant compute infrastructure capacity?"));
}),
_U1/* formItems136 */ = new T1(1,_U0/* Questionnaire.formItems137 */),
_U2/* formItems135 */ = {_:0,a:_U1/* Questionnaire.formItems136 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_U3/* formItems133 */ = new T2(4,_U2/* Questionnaire.formItems135 */,_TZ/* Questionnaire.formItems134 */),
_U4/* formItems132 */ = new T2(1,_U3/* Questionnaire.formItems133 */,_k/* GHC.Types.[] */),
_U5/* formItems138 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_U6/* formItems131 */ = new T3(7,_U5/* Questionnaire.formItems138 */,_Pz/* Questionnaire.formItems31 */,_U4/* Questionnaire.formItems132 */),
_U7/* formItems129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you do systems biology modeling?"));
}),
_U8/* formItems128 */ = new T1(1,_U7/* Questionnaire.formItems129 */),
_U9/* formItems127 */ = {_:0,a:_U8/* Questionnaire.formItems128 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ua/* formItems126 */ = new T2(4,_U9/* Questionnaire.formItems127 */,_Pl/* Questionnaire.formItems18 */),
_Ub/* formItems125 */ = new T2(1,_Ua/* Questionnaire.formItems126 */,_k/* GHC.Types.[] */),
_Uc/* formItems130 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ud/* formItems124 */ = new T3(7,_Uc/* Questionnaire.formItems130 */,_Pz/* Questionnaire.formItems31 */,_Ub/* Questionnaire.formItems125 */),
_Ue/* formItems120 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data analysis is normally done manually on a step-by-step basis. It is essential to make sure all steps are properly documented, otherwise results will not be reproducible.</p>"));
}),
_Uf/* formItems119 */ = new T1(1,_Ue/* Questionnaire.formItems120 */),
_Ug/* formItems122 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you be making sure there is good provenance of the data analysis?"));
}),
_Uh/* formItems121 */ = new T1(1,_Ug/* Questionnaire.formItems122 */),
_Ui/* formItems118 */ = {_:0,a:_Uh/* Questionnaire.formItems121 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Uf/* Questionnaire.formItems119 */,g:_Po/* Questionnaire.formItems25 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Uj/* formItems111 */ = new T2(4,_Ui/* Questionnaire.formItems118 */,_RO/* Questionnaire.formItems112 */),
_Uk/* formItems110 */ = new T2(1,_Uj/* Questionnaire.formItems111 */,_k/* GHC.Types.[] */),
_Ul/* formItems123 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Um/* formItems109 */ = new T3(7,_Ul/* Questionnaire.formItems123 */,_Pz/* Questionnaire.formItems31 */,_Uk/* Questionnaire.formItems110 */),
_Un/* formItems107 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you do structural modeling?"));
}),
_Uo/* formItems106 */ = new T1(1,_Un/* Questionnaire.formItems107 */),
_Up/* formItems105 */ = {_:0,a:_Uo/* Questionnaire.formItems106 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Uq/* formItems104 */ = new T2(4,_Up/* Questionnaire.formItems105 */,_Pl/* Questionnaire.formItems18 */),
_Ur/* formItems103 */ = new T2(1,_Uq/* Questionnaire.formItems104 */,_k/* GHC.Types.[] */),
_Us/* formItems108 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ut/* formItems102 */ = new T3(7,_Us/* Questionnaire.formItems108 */,_Pz/* Questionnaire.formItems31 */,_Ur/* Questionnaire.formItems103 */),
_Uu/* formItems101 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Uv/* formItems100 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be doing (automated) knowledge discovery?"));
}),
_Uw/* formItems99 */ = new T1(1,_Uv/* Questionnaire.formItems100 */),
_Ux/* formItems98 */ = {_:0,a:_Uw/* Questionnaire.formItems99 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Po/* Questionnaire.formItems25 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Uy/* formItems97 */ = new T2(4,_Ux/* Questionnaire.formItems98 */,_Pl/* Questionnaire.formItems18 */),
_Uz/* formItems96 */ = new T2(1,_Uy/* Questionnaire.formItems97 */,_k/* GHC.Types.[] */),
_UA/* formItems95 */ = new T3(7,_Uu/* Questionnaire.formItems101 */,_Pz/* Questionnaire.formItems31 */,_Uz/* Questionnaire.formItems96 */),
_UB/* formItems94 */ = new T2(1,_UA/* Questionnaire.formItems95 */,_k/* GHC.Types.[] */),
_UC/* formItems93 */ = new T2(1,_Ut/* Questionnaire.formItems102 */,_UB/* Questionnaire.formItems94 */),
_UD/* formItems92 */ = new T2(1,_Um/* Questionnaire.formItems109 */,_UC/* Questionnaire.formItems93 */),
_UE/* formItems91 */ = new T2(1,_Ud/* Questionnaire.formItems124 */,_UD/* Questionnaire.formItems92 */),
_UF/* formItems90 */ = new T2(1,_U6/* Questionnaire.formItems131 */,_UE/* Questionnaire.formItems91 */),
_UG/* formItems89 */ = new T2(6,_TY/* Questionnaire.formItems139 */,_UF/* Questionnaire.formItems90 */),
_UH/* formItems6 */ = new T2(1,_UG/* Questionnaire.formItems89 */,_TX/* Questionnaire.formItems7 */),
_UI/* formItems5 */ = new T2(1,_T0/* Questionnaire.formItems142 */,_UH/* Questionnaire.formItems6 */),
_UJ/* formItems4 */ = new T2(1,_Si/* Questionnaire.formItems184 */,_UI/* Questionnaire.formItems5 */),
_UK/* formItems3 */ = new T2(1,_Rv/* Questionnaire.formItems230 */,_UJ/* Questionnaire.formItems4 */),
_UL/* formItems2 */ = new T2(1,_QL/* Questionnaire.formItems276 */,_UK/* Questionnaire.formItems3 */),
_UM/* formItems353 */ = 38,
_UN/* formItems352 */ = new T1(1,_UM/* Questionnaire.formItems353 */),
_UO/* formItems355 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be collecting experimental data?"));
}),
_UP/* formItems354 */ = new T1(1,_UO/* Questionnaire.formItems355 */),
_UQ/* formItems351 */ = {_:0,a:_UP/* Questionnaire.formItems354 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_UN/* Questionnaire.formItems352 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_UR/* formItems350 */ = new T2(4,_UQ/* Questionnaire.formItems351 */,_Pl/* Questionnaire.formItems18 */),
_US/* formItems349 */ = new T2(1,_UR/* Questionnaire.formItems350 */,_k/* GHC.Types.[] */),
_UT/* formItems356 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_UN/* Questionnaire.formItems352 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_UU/* formItems348 */ = new T3(7,_UT/* Questionnaire.formItems356 */,_Pz/* Questionnaire.formItems31 */,_US/* Questionnaire.formItems349 */),
_UV/* formItems347 */ = new T2(1,_UU/* Questionnaire.formItems348 */,_k/* GHC.Types.[] */),
_UW/* formItems362 */ = 33,
_UX/* formItems361 */ = new T1(1,_UW/* Questionnaire.formItems362 */),
_UY/* formItems364 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be storing samples?"));
}),
_UZ/* formItems363 */ = new T1(1,_UY/* Questionnaire.formItems364 */),
_V0/* formItems360 */ = {_:0,a:_UZ/* Questionnaire.formItems363 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_UX/* Questionnaire.formItems361 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_V1/* formItems359 */ = new T2(4,_V0/* Questionnaire.formItems360 */,_Pl/* Questionnaire.formItems18 */),
_V2/* formItems358 */ = new T2(1,_V1/* Questionnaire.formItems359 */,_k/* GHC.Types.[] */),
_V3/* formItems365 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_UX/* Questionnaire.formItems361 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_V4/* formItems357 */ = new T3(7,_V3/* Questionnaire.formItems365 */,_Pz/* Questionnaire.formItems31 */,_V2/* Questionnaire.formItems358 */),
_V5/* formItems346 */ = new T2(1,_V4/* Questionnaire.formItems357 */,_UV/* Questionnaire.formItems347 */),
_V6/* formItems371 */ = 29,
_V7/* formItems370 */ = new T1(1,_V6/* Questionnaire.formItems371 */),
_V8/* formItems373 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will reference data be created?"));
}),
_V9/* formItems372 */ = new T1(1,_V8/* Questionnaire.formItems373 */),
_Va/* formItems369 */ = {_:0,a:_V9/* Questionnaire.formItems372 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_V7/* Questionnaire.formItems370 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Vb/* formItems368 */ = new T2(4,_Va/* Questionnaire.formItems369 */,_Pl/* Questionnaire.formItems18 */),
_Vc/* formItems367 */ = new T2(1,_Vb/* Questionnaire.formItems368 */,_k/* GHC.Types.[] */),
_Vd/* formItems374 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_V7/* Questionnaire.formItems370 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ve/* formItems366 */ = new T3(7,_Vd/* Questionnaire.formItems374 */,_Pz/* Questionnaire.formItems31 */,_Vc/* Questionnaire.formItems367 */),
_Vf/* formItems345 */ = new T2(1,_Ve/* Questionnaire.formItems366 */,_V5/* Questionnaire.formItems346 */),
_Vg/* formItems392 */ = 16,
_Vh/* formItems391 */ = new T1(1,_Vg/* Questionnaire.formItems392 */),
_Vi/* formItems394 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you are combining data from different sources, harmonization may be required. You may need to re-analyse some original data.</p>"));
}),
_Vj/* formItems393 */ = new T1(1,_Vi/* Questionnaire.formItems394 */),
_Vk/* formItems396 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to harmonize different sources of existing data?"));
}),
_Vl/* formItems395 */ = new T1(1,_Vk/* Questionnaire.formItems396 */),
_Vm/* formItems390 */ = {_:0,a:_Vl/* Questionnaire.formItems395 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Vj/* Questionnaire.formItems393 */,g:_Qx/* Questionnaire.formItems79 */,h:_Vh/* Questionnaire.formItems391 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Vn/* formItems389 */ = new T2(4,_Vm/* Questionnaire.formItems390 */,_Pl/* Questionnaire.formItems18 */),
_Vo/* formItems388 */ = new T2(1,_Vn/* Questionnaire.formItems389 */,_k/* GHC.Types.[] */),
_Vp/* formItems397 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Vh/* Questionnaire.formItems391 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Vq/* formItems387 */ = new T3(7,_Vp/* Questionnaire.formItems397 */,_Pz/* Questionnaire.formItems31 */,_Vo/* Questionnaire.formItems388 */),
_Vr/* formItems386 */ = new T2(1,_Vq/* Questionnaire.formItems387 */,_k/* GHC.Types.[] */),
_Vs/* formItems427 */ = 49,
_Vt/* formItems426 */ = new T1(1,_Vs/* Questionnaire.formItems427 */),
_Vu/* formItems429 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data sets that have similar but not identical fields or with identical fields that are not consistently filled can be coupled using probabilistic methods. Will you be using such methods?</p>"));
}),
_Vv/* formItems428 */ = new T1(1,_Vu/* Questionnaire.formItems429 */),
_Vw/* formItems431 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you use probabilistic couplings?"));
}),
_Vx/* formItems430 */ = new T1(1,_Vw/* Questionnaire.formItems431 */),
_Vy/* formItems425 */ = {_:0,a:_Vx/* Questionnaire.formItems430 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Vv/* Questionnaire.formItems428 */,g:_Qx/* Questionnaire.formItems79 */,h:_Vt/* Questionnaire.formItems426 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Vz/* formItems424 */ = new T2(4,_Vy/* Questionnaire.formItems425 */,_Pl/* Questionnaire.formItems18 */),
_VA/* formItems423 */ = new T2(1,_Vz/* Questionnaire.formItems424 */,_k/* GHC.Types.[] */),
_VB/* formItems432 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Vt/* Questionnaire.formItems426 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_VC/* formItems422 */ = new T3(7,_VB/* Questionnaire.formItems432 */,_Pz/* Questionnaire.formItems31 */,_VA/* Questionnaire.formItems423 */),
_VD/* formItems421 */ = new T2(1,_VC/* Questionnaire.formItems422 */,_k/* GHC.Types.[] */),
_VE/* formItems438 */ = 48,
_VF/* formItems437 */ = new T1(1,_VE/* Questionnaire.formItems438 */),
_VG/* formItems440 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What variable(s) will you be using for the coupling?"));
}),
_VH/* formItems439 */ = new T1(1,_VG/* Questionnaire.formItems440 */),
_VI/* formItems436 */ = {_:0,a:_VH/* Questionnaire.formItems439 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_VF/* Questionnaire.formItems437 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_VJ/* formItems435 */ = new T1(1,_VI/* Questionnaire.formItems436 */),
_VK/* formItems434 */ = new T2(1,_VJ/* Questionnaire.formItems435 */,_k/* GHC.Types.[] */),
_VL/* formItems441 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_VF/* Questionnaire.formItems437 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_VM/* formItems433 */ = new T3(7,_VL/* Questionnaire.formItems441 */,_Pz/* Questionnaire.formItems31 */,_VK/* Questionnaire.formItems434 */),
_VN/* formItems420 */ = new T2(1,_VM/* Questionnaire.formItems433 */,_VD/* Questionnaire.formItems421 */),
_VO/* formItems448 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Enlarging the group of subjects (union)"));
}),
_VP/* formItems447 */ = new T1(0,_VO/* Questionnaire.formItems448 */),
_VQ/* formItems446 */ = new T2(1,_VP/* Questionnaire.formItems447 */,_k/* GHC.Types.[] */),
_VR/* formItems450 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("More data about the same subjects (intersection)"));
}),
_VS/* formItems449 */ = new T1(0,_VR/* Questionnaire.formItems450 */),
_VT/* formItems445 */ = new T2(1,_VS/* Questionnaire.formItems449 */,_VQ/* Questionnaire.formItems446 */),
_VU/* formItems453 */ = 47,
_VV/* formItems452 */ = new T1(1,_VU/* Questionnaire.formItems453 */),
_VW/* formItems455 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What is the goal of the coupling?"));
}),
_VX/* formItems454 */ = new T1(1,_VW/* Questionnaire.formItems455 */),
_VY/* formItems451 */ = {_:0,a:_VX/* Questionnaire.formItems454 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_VV/* Questionnaire.formItems452 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_VZ/* formItems444 */ = new T2(4,_VY/* Questionnaire.formItems451 */,_VT/* Questionnaire.formItems445 */),
_W0/* formItems443 */ = new T2(1,_VZ/* Questionnaire.formItems444 */,_k/* GHC.Types.[] */),
_W1/* formItems456 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_VV/* Questionnaire.formItems452 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_W2/* formItems442 */ = new T3(7,_W1/* Questionnaire.formItems456 */,_Pz/* Questionnaire.formItems31 */,_W0/* Questionnaire.formItems443 */),
_W3/* formItems419 */ = new T2(1,_W2/* Questionnaire.formItems442 */,_VN/* Questionnaire.formItems420 */),
_W4/* formItems462 */ = 46,
_W5/* formItems461 */ = new T1(1,_W4/* Questionnaire.formItems462 */),
_W6/* formItems464 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sometimes, through the nature of the data sets that are coupled, the coupled set is no longer representative for the whole population (e.g. some fields may only have been filled for people with high blood pressure). This can disturb your research if undetected. How will you make sure this is not happening?"));
}),
_W7/* formItems463 */ = new T1(1,_W6/* Questionnaire.formItems464 */),
_W8/* formItems466 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you check whether your coupled data are representative of your goal population?"));
}),
_W9/* formItems465 */ = new T1(1,_W8/* Questionnaire.formItems466 */),
_Wa/* formItems460 */ = {_:0,a:_W9/* Questionnaire.formItems465 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_W7/* Questionnaire.formItems463 */,g:_Qx/* Questionnaire.formItems79 */,h:_W5/* Questionnaire.formItems461 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wb/* formItems459 */ = new T1(1,_Wa/* Questionnaire.formItems460 */),
_Wc/* formItems458 */ = new T2(1,_Wb/* Questionnaire.formItems459 */,_k/* GHC.Types.[] */),
_Wd/* formItems467 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_W5/* Questionnaire.formItems461 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_We/* formItems457 */ = new T3(7,_Wd/* Questionnaire.formItems467 */,_Pz/* Questionnaire.formItems31 */,_Wc/* Questionnaire.formItems458 */),
_Wf/* formItems418 */ = new T2(1,_We/* Questionnaire.formItems457 */,_W3/* Questionnaire.formItems419 */),
_Wg/* formItems473 */ = 45,
_Wh/* formItems472 */ = new T1(1,_Wg/* Questionnaire.formItems473 */),
_Wi/* formItems475 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is consent available for the couplings?"));
}),
_Wj/* formItems474 */ = new T1(1,_Wi/* Questionnaire.formItems475 */),
_Wk/* formItems471 */ = {_:0,a:_Wj/* Questionnaire.formItems474 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Wh/* Questionnaire.formItems472 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wl/* formItems470 */ = new T2(4,_Wk/* Questionnaire.formItems471 */,_Pl/* Questionnaire.formItems18 */),
_Wm/* formItems469 */ = new T2(1,_Wl/* Questionnaire.formItems470 */,_k/* GHC.Types.[] */),
_Wn/* formItems476 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Wh/* Questionnaire.formItems472 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wo/* formItems468 */ = new T3(7,_Wn/* Questionnaire.formItems476 */,_Pz/* Questionnaire.formItems31 */,_Wm/* Questionnaire.formItems469 */),
_Wp/* formItems417 */ = new T2(1,_Wo/* Questionnaire.formItems468 */,_Wf/* Questionnaire.formItems418 */),
_Wq/* formItems482 */ = 44,
_Wr/* formItems481 */ = new T1(1,_Wq/* Questionnaire.formItems482 */),
_Ws/* formItems484 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What will be the procedure that is followed? Where will what data be sent? Did a legal advisor look at the procedures?"));
}),
_Wt/* formItems483 */ = new T1(1,_Ws/* Questionnaire.formItems484 */),
_Wu/* formItems486 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using a trusted third party for coupling?"));
}),
_Wv/* formItems485 */ = new T1(1,_Wu/* Questionnaire.formItems486 */),
_Ww/* formItems480 */ = {_:0,a:_Wv/* Questionnaire.formItems485 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Wt/* Questionnaire.formItems483 */,g:_Qx/* Questionnaire.formItems79 */,h:_Wr/* Questionnaire.formItems481 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wx/* formItems479 */ = new T1(1,_Ww/* Questionnaire.formItems480 */),
_Wy/* formItems478 */ = new T2(1,_Wx/* Questionnaire.formItems479 */,_k/* GHC.Types.[] */),
_Wz/* formItems487 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Wr/* Questionnaire.formItems481 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WA/* formItems477 */ = new T3(7,_Wz/* Questionnaire.formItems487 */,_Pz/* Questionnaire.formItems31 */,_Wy/* Questionnaire.formItems478 */),
_WB/* formItems416 */ = new T2(1,_WA/* Questionnaire.formItems477 */,_Wp/* Questionnaire.formItems417 */),
_WC/* formItems493 */ = 43,
_WD/* formItems492 */ = new T1(1,_WC/* Questionnaire.formItems493 */),
_WE/* formItems495 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data sets that have exactly identical fields that are well filled can be coupled using deterministic methods. Will you be using such methods?</p>"));
}),
_WF/* formItems494 */ = new T1(1,_WE/* Questionnaire.formItems495 */),
_WG/* formItems497 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you use deterministic couplings?"));
}),
_WH/* formItems496 */ = new T1(1,_WG/* Questionnaire.formItems497 */),
_WI/* formItems491 */ = {_:0,a:_WH/* Questionnaire.formItems496 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_WF/* Questionnaire.formItems494 */,g:_Qx/* Questionnaire.formItems79 */,h:_WD/* Questionnaire.formItems492 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WJ/* formItems490 */ = new T2(4,_WI/* Questionnaire.formItems491 */,_Pl/* Questionnaire.formItems18 */),
_WK/* formItems489 */ = new T2(1,_WJ/* Questionnaire.formItems490 */,_k/* GHC.Types.[] */),
_WL/* formItems498 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_WD/* Questionnaire.formItems492 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WM/* formItems488 */ = new T3(7,_WL/* Questionnaire.formItems498 */,_Pz/* Questionnaire.formItems31 */,_WK/* Questionnaire.formItems489 */),
_WN/* formItems415 */ = new T2(1,_WM/* Questionnaire.formItems488 */,_WB/* Questionnaire.formItems416 */),
_WO/* formItems501 */ = 42,
_WP/* formItems500 */ = new T1(1,_WO/* Questionnaire.formItems501 */),
_WQ/* formItems499 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_WP/* Questionnaire.formItems500 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WR/* formItems414 */ = new T3(7,_WQ/* Questionnaire.formItems499 */,_Pz/* Questionnaire.formItems31 */,_WN/* Questionnaire.formItems415 */),
_WS/* formItems413 */ = new T2(1,_WR/* Questionnaire.formItems414 */,_k/* GHC.Types.[] */),
_WT/* formItems412 */ = new T3(1,_Pm/* FormEngine.FormItem.NoNumbering */,_Pg/* Questionnaire.formItems21 */,_WS/* Questionnaire.formItems413 */),
_WU/* formItems411 */ = new T2(1,_WT/* Questionnaire.formItems412 */,_k/* GHC.Types.[] */),
_WV/* formItems410 */ = new T2(1,_Pk/* Questionnaire.formItems22 */,_WU/* Questionnaire.formItems411 */),
_WW/* formItems504 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you couple existing (biobank) data sets?"));
}),
_WX/* formItems503 */ = new T1(1,_WW/* Questionnaire.formItems504 */),
_WY/* formItems502 */ = {_:0,a:_WX/* Questionnaire.formItems503 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_WP/* Questionnaire.formItems500 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WZ/* formItems409 */ = new T2(4,_WY/* Questionnaire.formItems502 */,_WV/* Questionnaire.formItems410 */),
_X0/* formItems408 */ = new T2(1,_WZ/* Questionnaire.formItems409 */,_k/* GHC.Types.[] */),
_X1/* formItems407 */ = new T3(7,_WQ/* Questionnaire.formItems499 */,_Pz/* Questionnaire.formItems31 */,_X0/* Questionnaire.formItems408 */),
_X2/* formItems406 */ = new T2(1,_X1/* Questionnaire.formItems407 */,_k/* GHC.Types.[] */),
_X3/* formItems516 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New consent needed"));
}),
_X4/* formItems515 */ = new T1(0,_X3/* Questionnaire.formItems516 */),
_X5/* formItems514 */ = new T2(1,_X4/* Questionnaire.formItems515 */,_k/* GHC.Types.[] */),
_X6/* formItems518 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Existing consent applies"));
}),
_X7/* formItems517 */ = new T1(0,_X6/* Questionnaire.formItems518 */),
_X8/* formItems513 */ = new T2(1,_X7/* Questionnaire.formItems517 */,_X5/* Questionnaire.formItems514 */),
_X9/* formItems520 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Not applicable"));
}),
_Xa/* formItems519 */ = new T1(0,_X9/* Questionnaire.formItems520 */),
_Xb/* formItems512 */ = new T2(1,_Xa/* Questionnaire.formItems519 */,_X8/* Questionnaire.formItems513 */),
_Xc/* formItems523 */ = 12,
_Xd/* formItems522 */ = new T1(1,_Xc/* Questionnaire.formItems523 */),
_Xe/* formItems525 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If the data that you will re-use is coupled to people, is the informed consent that was originally obtained from those people covering your current research?</p>"));
}),
_Xf/* formItems524 */ = new T1(1,_Xe/* Questionnaire.formItems525 */),
_Xg/* formItems527 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is extenstion of any consent for privacy sensitive data be needed?"));
}),
_Xh/* formItems526 */ = new T1(1,_Xg/* Questionnaire.formItems527 */),
_Xi/* formItems521 */ = {_:0,a:_Xh/* Questionnaire.formItems526 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Xf/* Questionnaire.formItems524 */,g:_Qx/* Questionnaire.formItems79 */,h:_Xd/* Questionnaire.formItems522 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Xj/* formItems511 */ = new T2(4,_Xi/* Questionnaire.formItems521 */,_Xb/* Questionnaire.formItems512 */),
_Xk/* formItems510 */ = new T2(1,_Xj/* Questionnaire.formItems511 */,_k/* GHC.Types.[] */),
_Xl/* formItems528 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Xd/* Questionnaire.formItems522 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Xm/* formItems509 */ = new T3(7,_Xl/* Questionnaire.formItems528 */,_Pz/* Questionnaire.formItems31 */,_Xk/* Questionnaire.formItems510 */),
_Xn/* formItems508 */ = new T2(1,_Xm/* Questionnaire.formItems509 */,_k/* GHC.Types.[] */),
_Xo/* formItems536 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We are the owners"));
}),
_Xp/* formItems535 */ = new T1(0,_Xo/* Questionnaire.formItems536 */),
_Xq/* formItems534 */ = new T2(1,_Xp/* Questionnaire.formItems535 */,_k/* GHC.Types.[] */),
_Xr/* formItems533 */ = new T2(1,_Ph/* Questionnaire.formItems20 */,_Xq/* Questionnaire.formItems534 */),
_Xs/* formItems532 */ = new T2(1,_Pk/* Questionnaire.formItems22 */,_Xr/* Questionnaire.formItems533 */),
_Xt/* formItems539 */ = 11,
_Xu/* formItems538 */ = new T1(1,_Xt/* Questionnaire.formItems539 */),
_Xv/* formItems541 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the owners of this data set work with you on this study"));
}),
_Xw/* formItems540 */ = new T1(1,_Xv/* Questionnaire.formItems541 */),
_Xx/* formItems537 */ = {_:0,a:_Xw/* Questionnaire.formItems540 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Xu/* Questionnaire.formItems538 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Xy/* formItems531 */ = new T2(4,_Xx/* Questionnaire.formItems537 */,_Xs/* Questionnaire.formItems532 */),
_Xz/* formItems530 */ = new T2(1,_Xy/* Questionnaire.formItems531 */,_k/* GHC.Types.[] */),
_XA/* formItems542 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Xu/* Questionnaire.formItems538 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_XB/* formItems529 */ = new T3(7,_XA/* Questionnaire.formItems542 */,_Pz/* Questionnaire.formItems31 */,_Xz/* Questionnaire.formItems530 */),
_XC/* formItems507 */ = new T2(1,_XB/* Questionnaire.formItems529 */,_Xn/* Questionnaire.formItems508 */),
_XD/* formItems548 */ = 9,
_XE/* formItems547 */ = new T1(1,_XD/* Questionnaire.formItems548 */),
_XF/* formItems550 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Even if you will be producing your own data, you often will also be relying on existing data sets. You may need to integrate your new data with an existing data set or retrieve additional information from related data bases. Will you be doing such things?</p>"));
}),
_XG/* formItems549 */ = new T1(1,_XF/* Questionnaire.formItems550 */),
_XH/* formItems552 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Write each item on new line"));
}),
_XI/* formItems551 */ = new T1(1,_XH/* Questionnaire.formItems552 */),
_XJ/* formItems554 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Items"));
}),
_XK/* formItems553 */ = new T1(1,_XJ/* Questionnaire.formItems554 */),
_XL/* formItems546 */ = {_:0,a:_XK/* Questionnaire.formItems553 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_XI/* Questionnaire.formItems551 */,f:_XG/* Questionnaire.formItems549 */,g:_Qx/* Questionnaire.formItems79 */,h:_XE/* Questionnaire.formItems547 */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_XM/* formItems545 */ = new T1(1,_XL/* Questionnaire.formItems546 */),
_XN/* formItems544 */ = new T2(1,_XM/* Questionnaire.formItems545 */,_k/* GHC.Types.[] */),
_XO/* formItems557 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What existing non-reference data sets will you use?"));
}),
_XP/* formItems556 */ = new T1(1,_XO/* Questionnaire.formItems557 */),
_XQ/* formItems555 */ = {_:0,a:_XP/* Questionnaire.formItems556 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_XG/* Questionnaire.formItems549 */,g:_Qx/* Questionnaire.formItems79 */,h:_XE/* Questionnaire.formItems547 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_XR/* formItems543 */ = new T3(7,_XQ/* Questionnaire.formItems555 */,_Pz/* Questionnaire.formItems31 */,_XN/* Questionnaire.formItems544 */),
_XS/* formItems506 */ = new T2(1,_XR/* Questionnaire.formItems543 */,_XC/* Questionnaire.formItems507 */),
_XT/* formItems558 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_XE/* Questionnaire.formItems547 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_XU/* formItems505 */ = new T3(7,_XT/* Questionnaire.formItems558 */,_Pz/* Questionnaire.formItems31 */,_XS/* Questionnaire.formItems506 */),
_XV/* formItems405 */ = new T2(1,_XU/* Questionnaire.formItems505 */,_X2/* Questionnaire.formItems406 */),
_XW/* formItems581 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("All analyses will be redone with the new version"));
}),
_XX/* formItems580 */ = new T1(0,_XW/* Questionnaire.formItems581 */),
_XY/* formItems579 */ = new T2(1,_XX/* Questionnaire.formItems580 */,_k/* GHC.Types.[] */),
_XZ/* formItems583 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New analyses will be done with the new version"));
}),
_Y0/* formItems582 */ = new T1(0,_XZ/* Questionnaire.formItems583 */),
_Y1/* formItems578 */ = new T2(1,_Y0/* Questionnaire.formItems582 */,_XY/* Questionnaire.formItems579 */),
_Y2/* formItems585 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will stay with the old version"));
}),
_Y3/* formItems584 */ = new T1(0,_Y2/* Questionnaire.formItems585 */),
_Y4/* formItems577 */ = new T2(1,_Y3/* Questionnaire.formItems584 */,_Y1/* Questionnaire.formItems578 */),
_Y5/* formItems588 */ = 8,
_Y6/* formItems587 */ = new T1(1,_Y5/* Questionnaire.formItems588 */),
_Y7/* formItems590 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If the reference changes while you are working on your research project, you need to decide whether you will follow these changes. Most likely that will mean that you have to do some analyses again, so you will need to make sure enough resources are available to do so. You can decide to stay with the version that you started with; this can have the disadvantage that you will not benefit from added information or added consistency.</p>"));
}),
_Y8/* formItems589 */ = new T1(1,_Y7/* Questionnaire.formItems590 */),
_Y9/* formItems592 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you change version if it updates?"));
}),
_Ya/* formItems591 */ = new T1(1,_Y9/* Questionnaire.formItems592 */),
_Yb/* formItems586 */ = {_:0,a:_Ya/* Questionnaire.formItems591 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Y8/* Questionnaire.formItems589 */,g:_Qx/* Questionnaire.formItems79 */,h:_Y6/* Questionnaire.formItems587 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Yc/* formItems576 */ = new T2(4,_Yb/* Questionnaire.formItems586 */,_Y4/* Questionnaire.formItems577 */),
_Yd/* formItems575 */ = new T2(1,_Yc/* Questionnaire.formItems576 */,_k/* GHC.Types.[] */),
_Ye/* formItems593 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Y6/* Questionnaire.formItems587 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Yf/* formItems574 */ = new T3(7,_Ye/* Questionnaire.formItems593 */,_Pz/* Questionnaire.formItems31 */,_Yd/* Questionnaire.formItems575 */),
_Yg/* formItems573 */ = new T2(1,_Yf/* Questionnaire.formItems574 */,_k/* GHC.Types.[] */),
_Yh/* formItems599 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("If there are different versions available, you have to decide with all project partners together which version you will be using. Probably you will go for the latest release as of the date of the start of your research project. However, if you have other data from older projects that need to be merged, you may need to consider using the same release you used for a previous project."));
}),
_Yi/* formItems598 */ = new T1(1,_Yh/* Questionnaire.formItems599 */),
_Yj/* formItems601 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Which version will you use?"));
}),
_Yk/* formItems600 */ = new T1(1,_Yj/* Questionnaire.formItems601 */),
_Yl/* formItems597 */ = {_:0,a:_Yk/* Questionnaire.formItems600 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Yi/* Questionnaire.formItems598 */,g:_Qx/* Questionnaire.formItems79 */,h:_T2/* Questionnaire.formItems27 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ym/* formItems596 */ = new T1(1,_Yl/* Questionnaire.formItems597 */),
_Yn/* formItems595 */ = new T2(1,_Ym/* Questionnaire.formItems596 */,_k/* GHC.Types.[] */),
_Yo/* formItems602 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_T2/* Questionnaire.formItems27 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Yp/* formItems594 */ = new T3(7,_Yo/* Questionnaire.formItems602 */,_Pz/* Questionnaire.formItems31 */,_Yn/* Questionnaire.formItems595 */),
_Yq/* formItems572 */ = new T2(1,_Yp/* Questionnaire.formItems594 */,_Yg/* Questionnaire.formItems573 */),
_Yr/* formItems603 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Po/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ys/* formItems571 */ = new T3(7,_Yr/* Questionnaire.formItems603 */,_Pz/* Questionnaire.formItems31 */,_Yq/* Questionnaire.formItems572 */),
_Yt/* formItems570 */ = new T2(1,_Ys/* Questionnaire.formItems571 */,_k/* GHC.Types.[] */),
_Yu/* formItems569 */ = new T3(1,_Pm/* FormEngine.FormItem.NoNumbering */,_Pg/* Questionnaire.formItems21 */,_Yt/* Questionnaire.formItems570 */),
_Yv/* formItems568 */ = new T2(1,_Yu/* Questionnaire.formItems569 */,_k/* GHC.Types.[] */),
_Yw/* formItems567 */ = new T2(1,_Pk/* Questionnaire.formItems22 */,_Yv/* Questionnaire.formItems568 */),
_Yx/* formItems606 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Many reference data sets evolve over time. If the reference data set changes, this may affect your results. If different versions of a reference data set exist, you need to establish your \"version policy\".</p>"));
}),
_Yy/* formItems605 */ = new T1(1,_Yx/* Questionnaire.formItems606 */),
_Yz/* formItems608 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the reference data resource versioned?"));
}),
_YA/* formItems607 */ = new T1(1,_Yz/* Questionnaire.formItems608 */),
_YB/* formItems604 */ = {_:0,a:_YA/* Questionnaire.formItems607 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Yy/* Questionnaire.formItems605 */,g:_Qx/* Questionnaire.formItems79 */,h:_Po/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_YC/* formItems566 */ = new T2(4,_YB/* Questionnaire.formItems604 */,_Yw/* Questionnaire.formItems567 */),
_YD/* formItems565 */ = new T2(1,_YC/* Questionnaire.formItems566 */,_k/* GHC.Types.[] */),
_YE/* formItems564 */ = new T3(7,_Yr/* Questionnaire.formItems603 */,_Pz/* Questionnaire.formItems31 */,_YD/* Questionnaire.formItems565 */),
_YF/* formItems563 */ = new T2(1,_YE/* Questionnaire.formItems564 */,_k/* GHC.Types.[] */),
_YG/* formItems615 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I need to convert it before using"));
}),
_YH/* formItems614 */ = new T1(0,_YG/* Questionnaire.formItems615 */),
_YI/* formItems613 */ = new T2(1,_YH/* Questionnaire.formItems614 */,_k/* GHC.Types.[] */),
_YJ/* formItems617 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I can directly use it"));
}),
_YK/* formItems616 */ = new T1(0,_YJ/* Questionnaire.formItems617 */),
_YL/* formItems612 */ = new T2(1,_YK/* Questionnaire.formItems616 */,_YI/* Questionnaire.formItems613 */),
_YM/* formItems620 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Do you know the data format of the reference data? Is this suitable for your work? Does it need to be converted?</p>"));
}),
_YN/* formItems619 */ = new T1(1,_YM/* Questionnaire.formItems620 */),
_YO/* formItems622 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("In what format is the reference data available?"));
}),
_YP/* formItems621 */ = new T1(1,_YO/* Questionnaire.formItems622 */),
_YQ/* formItems618 */ = {_:0,a:_YP/* Questionnaire.formItems621 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_YN/* Questionnaire.formItems619 */,g:_Qx/* Questionnaire.formItems79 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_YR/* formItems611 */ = new T2(4,_YQ/* Questionnaire.formItems618 */,_YL/* Questionnaire.formItems612 */),
_YS/* formItems610 */ = new T2(1,_YR/* Questionnaire.formItems611 */,_k/* GHC.Types.[] */),
_YT/* formItems623 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_PL/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_YU/* formItems609 */ = new T3(7,_YT/* Questionnaire.formItems623 */,_Pz/* Questionnaire.formItems31 */,_YS/* Questionnaire.formItems610 */),
_YV/* formItems562 */ = new T2(1,_YU/* Questionnaire.formItems609 */,_YF/* Questionnaire.formItems563 */),
_YW/* formItems629 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Do you know where the reference data is available, what the conditions for use are, and how to reference it?</p>"));
}),
_YX/* formItems628 */ = new T1(1,_YW/* Questionnaire.formItems629 */),
_YY/* formItems631 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Where is it available?"));
}),
_YZ/* formItems630 */ = new T1(1,_YY/* Questionnaire.formItems631 */),
_Z0/* formItems627 */ = {_:0,a:_YZ/* Questionnaire.formItems630 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_YX/* Questionnaire.formItems628 */,g:_Qx/* Questionnaire.formItems79 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Z1/* formItems626 */ = new T2(4,_Z0/* Questionnaire.formItems627 */,_Pl/* Questionnaire.formItems18 */),
_Z2/* formItems625 */ = new T2(1,_Z1/* Questionnaire.formItems626 */,_k/* GHC.Types.[] */),
_Z3/* formItems632 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_PX/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Z4/* formItems624 */ = new T3(7,_Z3/* Questionnaire.formItems632 */,_Pz/* Questionnaire.formItems31 */,_Z2/* Questionnaire.formItems625 */),
_Z5/* formItems561 */ = new T2(1,_Z4/* Questionnaire.formItems624 */,_YV/* Questionnaire.formItems562 */),
_Z6/* formItems638 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Much of todays data is used in comparison with reference data. A genome for instance is compared with a reference genome to identify genomic variants. If you use reference data, there are several other issues that you should consider. What are the reference data sets that you will use?</p>"));
}),
_Z7/* formItems637 */ = new T1(1,_Z6/* Questionnaire.formItems638 */),
_Z8/* formItems636 */ = {_:0,a:_XK/* Questionnaire.formItems553 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_XI/* Questionnaire.formItems551 */,f:_Z7/* Questionnaire.formItems637 */,g:_Qx/* Questionnaire.formItems79 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_Z9/* formItems635 */ = new T1(1,_Z8/* Questionnaire.formItems636 */),
_Za/* formItems634 */ = new T2(1,_Z9/* Questionnaire.formItems635 */,_k/* GHC.Types.[] */),
_Zb/* formItems641 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What reference data will you use?"));
}),
_Zc/* formItems640 */ = new T1(1,_Zb/* Questionnaire.formItems641 */),
_Zd/* formItems639 */ = {_:0,a:_Zc/* Questionnaire.formItems640 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Z7/* Questionnaire.formItems637 */,g:_Qx/* Questionnaire.formItems79 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ze/* formItems633 */ = new T3(7,_Zd/* Questionnaire.formItems639 */,_Pz/* Questionnaire.formItems31 */,_Za/* Questionnaire.formItems634 */),
_Zf/* formItems560 */ = new T2(1,_Ze/* Questionnaire.formItems633 */,_Z5/* Questionnaire.formItems561 */),
_Zg/* formItems642 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Qf/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zh/* formItems559 */ = new T3(7,_Zg/* Questionnaire.formItems642 */,_Pz/* Questionnaire.formItems31 */,_Zf/* Questionnaire.formItems560 */),
_Zi/* formItems404 */ = new T2(1,_Zh/* Questionnaire.formItems559 */,_XV/* Questionnaire.formItems405 */),
_Zj/* formItems643 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zk/* formItems403 */ = new T3(7,_Zj/* Questionnaire.formItems643 */,_Pz/* Questionnaire.formItems31 */,_Zi/* Questionnaire.formItems404 */),
_Zl/* formItems402 */ = new T2(1,_Zk/* Questionnaire.formItems403 */,_k/* GHC.Types.[] */),
_Zm/* formItems401 */ = new T3(1,_Pm/* FormEngine.FormItem.NoNumbering */,_Pg/* Questionnaire.formItems21 */,_Zl/* Questionnaire.formItems402 */),
_Zn/* formItems400 */ = new T2(1,_Zm/* Questionnaire.formItems401 */,_k/* GHC.Types.[] */),
_Zo/* formItems399 */ = new T2(1,_Pk/* Questionnaire.formItems22 */,_Zn/* Questionnaire.formItems400 */),
_Zp/* formItems646 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Will you be referring to any earlier measured data, reference data, or data that should be mined from existing literature? Your own data as well as data from others?</p>"));
}),
_Zq/* formItems645 */ = new T1(1,_Zp/* Questionnaire.formItems646 */),
_Zr/* formItems648 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using any pre-existing data (including other people\'s data)?"));
}),
_Zs/* formItems647 */ = new T1(1,_Zr/* Questionnaire.formItems648 */),
_Zt/* formItems644 */ = {_:0,a:_Zs/* Questionnaire.formItems647 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Zq/* Questionnaire.formItems645 */,g:_Qx/* Questionnaire.formItems79 */,h:_Pu/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zu/* formItems398 */ = new T2(4,_Zt/* Questionnaire.formItems644 */,_Zo/* Questionnaire.formItems399 */),
_Zv/* formItems385 */ = new T2(1,_Zu/* Questionnaire.formItems398 */,_Vr/* Questionnaire.formItems386 */),
_Zw/* formItems384 */ = new T3(7,_Zj/* Questionnaire.formItems643 */,_Pz/* Questionnaire.formItems31 */,_Zv/* Questionnaire.formItems385 */),
_Zx/* formItems383 */ = new T2(1,_Zw/* Questionnaire.formItems384 */,_k/* GHC.Types.[] */),
_Zy/* formItems649 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Qx/* Questionnaire.formItems79 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zz/* formItems382 */ = new T3(7,_Zy/* Questionnaire.formItems649 */,_Pz/* Questionnaire.formItems31 */,_Zx/* Questionnaire.formItems383 */),
_ZA/* formItems381 */ = new T2(1,_Zz/* Questionnaire.formItems382 */,_k/* GHC.Types.[] */),
_ZB/* formItems380 */ = new T3(1,_Pm/* FormEngine.FormItem.NoNumbering */,_Pg/* Questionnaire.formItems21 */,_ZA/* Questionnaire.formItems381 */),
_ZC/* formItems379 */ = new T2(1,_ZB/* Questionnaire.formItems380 */,_k/* GHC.Types.[] */),
_ZD/* formItems378 */ = new T2(1,_Pk/* Questionnaire.formItems22 */,_ZC/* Questionnaire.formItems379 */),
_ZE/* formItems652 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Are there any data sets available in the world that are relevant to your planned research?</p>"));
}),
_ZF/* formItems651 */ = new T1(1,_ZE/* Questionnaire.formItems652 */),
_ZG/* formItems654 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is there any pre-existing data?"));
}),
_ZH/* formItems653 */ = new T1(1,_ZG/* Questionnaire.formItems654 */),
_ZI/* formItems650 */ = {_:0,a:_ZH/* Questionnaire.formItems653 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_ZF/* Questionnaire.formItems651 */,g:_Qx/* Questionnaire.formItems79 */,h:_Qx/* Questionnaire.formItems79 */,i:_4y/* GHC.Base.Nothing */,j:_8F/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_ZJ/* formItems377 */ = new T2(4,_ZI/* Questionnaire.formItems650 */,_ZD/* Questionnaire.formItems378 */),
_ZK/* formItems376 */ = new T2(1,_ZJ/* Questionnaire.formItems377 */,_k/* GHC.Types.[] */),
_ZL/* formItems375 */ = new T3(7,_Zy/* Questionnaire.formItems649 */,_Pz/* Questionnaire.formItems31 */,_ZK/* Questionnaire.formItems376 */),
_ZM/* formItems344 */ = new T2(1,_ZL/* Questionnaire.formItems375 */,_Vf/* Questionnaire.formItems345 */),
_ZN/* formItems657 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Before you decide to embark on any new study, it is nowadays good practice to consider all options to keep the data generation part of your study as limited as possible. It is not because we can generate massive amounts of data that we always need to do so. Creating data with public money is bringing with it the responsibility to treat those data well and (if potentially useful) make them available for re-use by others."));
}),
_ZO/* formItems656 */ = new T1(1,_ZN/* Questionnaire.formItems657 */),
_ZP/* formItems659 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Design of experiment"));
}),
_ZQ/* formItems658 */ = new T1(1,_ZP/* Questionnaire.formItems659 */),
_ZR/* formItems655 */ = {_:0,a:_ZQ/* Questionnaire.formItems658 */,b:_Pm/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_QJ/* Questionnaire.formItems85 */,f:_ZO/* Questionnaire.formItems656 */,g:_Qx/* Questionnaire.formItems79 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_ZS/* formItems343 */ = new T2(6,_ZR/* Questionnaire.formItems655 */,_ZM/* Questionnaire.formItems344 */),
_ZT/* formItems1 */ = new T2(1,_ZS/* Questionnaire.formItems343 */,_UL/* Questionnaire.formItems2 */),
_ZU/* prepareForm_xs */ = new T(function(){
  return new T2(1,_51/* FormEngine.FormItem.$fShowNumbering2 */,_ZU/* FormEngine.FormItem.prepareForm_xs */);
}),
_ZV/* prepareForm1 */ = new T2(1,_ZU/* FormEngine.FormItem.prepareForm_xs */,_51/* FormEngine.FormItem.$fShowNumbering2 */),
_ZW/* formItems */ = new T(function(){
  return E(B(_P5/* FormEngine.FormItem.$wgo1 */(_ZT/* Questionnaire.formItems1 */, _ZV/* FormEngine.FormItem.prepareForm1 */, _k/* GHC.Types.[] */)).b);
}),
_ZX/* lookup */ = function(_ZY/* s9uF */, _ZZ/* s9uG */, _100/* s9uH */){
  while(1){
    var _101/* s9uI */ = E(_100/* s9uH */);
    if(!_101/* s9uI */._){
      return __Z/* EXTERNAL */;
    }else{
      var _102/* s9uL */ = E(_101/* s9uI */.a);
      if(!B(A3(_en/* GHC.Classes.== */,_ZY/* s9uF */, _ZZ/* s9uG */, _102/* s9uL */.a))){
        _100/* s9uH */ = _101/* s9uI */.b;
        continue;
      }else{
        return new T1(1,_102/* s9uL */.b);
      }
    }
  }
},
_103/* getMaybeNumberFIUnitValue */ = function(_104/* s9dT */, _105/* s9dU */){
  var _106/* s9dV */ = E(_105/* s9dU */);
  if(!_106/* s9dV */._){
    return __Z/* EXTERNAL */;
  }else{
    var _107/* s9dX */ = E(_104/* s9dT */);
    if(_107/* s9dX */._==3){
      var _108/* s9e1 */ = E(_107/* s9dX */.b);
      switch(_108/* s9e1 */._){
        case 0:
          return new T1(1,_108/* s9e1 */.a);
        case 1:
          return new F(function(){return _ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(E(_107/* s9dX */.a).b)), _8j/* FormEngine.FormItem.nfiUnitId1 */));
          }), _106/* s9dV */.a);});
          break;
        default:
          return __Z/* EXTERNAL */;
      }
    }else{
      return E(_qV/* FormEngine.FormItem.nfiUnit1 */);
    }
  }
},
_109/* fiId */ = function(_10a/* s4XR */){
  return new F(function(){return _27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_10a/* s4XR */)).b);});
},
_10b/* isCheckboxChecked1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("on"));
}),
_10c/* isCheckboxChecked */ = function(_10d/* s9dM */, _10e/* s9dN */){
  var _10f/* s9dO */ = E(_10e/* s9dN */);
  if(!_10f/* s9dO */._){
    return false;
  }else{
    var _10g/* s9dR */ = B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_109/* FormEngine.FormItem.fiId */(_10d/* s9dM */));
    }), _10f/* s9dO */.a));
    if(!_10g/* s9dR */._){
      return false;
    }else{
      return new F(function(){return _2n/* GHC.Base.eqString */(_10g/* s9dR */.a, _10b/* FormEngine.FormData.isCheckboxChecked1 */);});
    }
  }
},
_10h/* isOptionSelected */ = function(_10i/* s9di */, _10j/* s9dj */, _10k/* s9dk */){
  var _10l/* s9dl */ = E(_10k/* s9dk */);
  if(!_10l/* s9dl */._){
    return false;
  }else{
    var _10m/* s9dA */ = B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_10j/* s9dj */)).b));
    }), _10l/* s9dl */.a));
    if(!_10m/* s9dA */._){
      return false;
    }else{
      var _10n/* s9dB */ = _10m/* s9dA */.a,
      _10o/* s9dC */ = E(_10i/* s9di */);
      if(!_10o/* s9dC */._){
        return new F(function(){return _2n/* GHC.Base.eqString */(_10n/* s9dB */, _10o/* s9dC */.a);});
      }else{
        return new F(function(){return _2n/* GHC.Base.eqString */(_10n/* s9dB */, _10o/* s9dC */.b);});
      }
    }
  }
},
_10p/* maybeStr2maybeInt2 */ = new T(function(){
  return B(A3(_mm/* GHC.Read.$fReadInt3 */,_mP/* GHC.Read.$fReadInt_$sconvertInt */, _lR/* Text.ParserCombinators.ReadPrec.minPrec */, _aY/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_10q/* maybeStr2maybeInt1 */ = function(_10r/* sc01 */){
  var _10s/* sc02 */ = B(_8r/* Text.ParserCombinators.ReadP.run */(_10p/* FormEngine.FormElement.FormElement.maybeStr2maybeInt2 */, _10r/* sc01 */));
  return (_10s/* sc02 */._==0) ? __Z/* EXTERNAL */ : (E(_10s/* sc02 */.b)._==0) ? new T1(1,E(_10s/* sc02 */.a).a) : __Z/* EXTERNAL */;
},
_10t/* makeElem */ = function(_10u/* sc0e */, _10v/* sc0f */, _10w/* sc0g */){
  var _10x/* sc0h */ = E(_10w/* sc0g */);
  switch(_10x/* sc0h */._){
    case 0:
      var _10y/* sc0A */ = new T(function(){
        var _10z/* sc0j */ = E(_10v/* sc0f */);
        if(!_10z/* sc0j */._){
          return __Z/* EXTERNAL */;
        }else{
          var _10A/* sc0y */ = B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_10x/* sc0h */.a).b));
          }), _10z/* sc0j */.a));
          if(!_10A/* sc0y */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_10A/* sc0y */.a);
          }
        }
      });
      return new T1(1,new T3(1,_10x/* sc0h */,_10y/* sc0A */,_10u/* sc0e */));
    case 1:
      var _10B/* sc0U */ = new T(function(){
        var _10C/* sc0D */ = E(_10v/* sc0f */);
        if(!_10C/* sc0D */._){
          return __Z/* EXTERNAL */;
        }else{
          var _10D/* sc0S */ = B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_10x/* sc0h */.a).b));
          }), _10C/* sc0D */.a));
          if(!_10D/* sc0S */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_10D/* sc0S */.a);
          }
        }
      });
      return new T1(1,new T3(2,_10x/* sc0h */,_10B/* sc0U */,_10u/* sc0e */));
    case 2:
      var _10E/* sc1e */ = new T(function(){
        var _10F/* sc0X */ = E(_10v/* sc0f */);
        if(!_10F/* sc0X */._){
          return __Z/* EXTERNAL */;
        }else{
          var _10G/* sc1c */ = B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_10x/* sc0h */.a).b));
          }), _10F/* sc0X */.a));
          if(!_10G/* sc1c */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_10G/* sc1c */.a);
          }
        }
      });
      return new T1(1,new T3(3,_10x/* sc0h */,_10E/* sc1e */,_10u/* sc0e */));
    case 3:
      var _10H/* sc1z */ = new T(function(){
        var _10I/* sc1i */ = E(_10v/* sc0f */);
        if(!_10I/* sc1i */._){
          return __Z/* EXTERNAL */;
        }else{
          var _10J/* sc1x */ = B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_10x/* sc0h */.a).b));
          }), _10I/* sc1i */.a));
          if(!_10J/* sc1x */._){
            return __Z/* EXTERNAL */;
          }else{
            return B(_10q/* FormEngine.FormElement.FormElement.maybeStr2maybeInt1 */(_10J/* sc1x */.a));
          }
        }
      });
      return new T1(1,new T4(4,_10x/* sc0h */,_10H/* sc1z */,new T(function(){
        return B(_103/* FormEngine.FormData.getMaybeNumberFIUnitValue */(_10x/* sc0h */, _10v/* sc0f */));
      }),_10u/* sc0e */));
    case 4:
      var _10K/* sc1E */ = new T(function(){
        return new T3(5,_10x/* sc0h */,_10L/* sc1F */,_10u/* sc0e */);
      }),
      _10L/* sc1F */ = new T(function(){
        var _10M/* sc1R */ = function(_10N/* sc1G */){
          var _10O/* sc1H */ = E(_10N/* sc1G */);
          if(!_10O/* sc1H */._){
            return new T2(0,_10O/* sc1H */,new T(function(){
              return B(_10h/* FormEngine.FormData.isOptionSelected */(_10O/* sc1H */, _10x/* sc0h */, _10v/* sc0f */));
            }));
          }else{
            var _10P/* sc1Q */ = new T(function(){
              return B(_pa/* Data.Maybe.catMaybes1 */(B(_8G/* GHC.Base.map */(function(_10Q/* B1 */){
                return new F(function(){return _10t/* FormEngine.FormElement.FormElement.makeElem */(_10K/* sc1E */, _10v/* sc0f */, _10Q/* B1 */);});
              }, _10O/* sc1H */.c))));
            });
            return new T3(1,_10O/* sc1H */,new T(function(){
              return B(_10h/* FormEngine.FormData.isOptionSelected */(_10O/* sc1H */, _10x/* sc0h */, _10v/* sc0f */));
            }),_10P/* sc1Q */);
          }
        };
        return B(_8G/* GHC.Base.map */(_10M/* sc1R */, _10x/* sc0h */.b));
      });
      return new T1(1,_10K/* sc1E */);
    case 5:
      var _10R/* sc29 */ = new T(function(){
        var _10S/* sc1U */ = E(_10v/* sc0f */);
        if(!_10S/* sc1U */._){
          return __Z/* EXTERNAL */;
        }else{
          return B(_ZX/* GHC.List.lookup */(_aL/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_10x/* sc0h */.a).b));
          }), _10S/* sc1U */.a));
        }
      });
      return new T1(1,new T3(6,_10x/* sc0h */,_10R/* sc29 */,_10u/* sc0e */));
    case 6:
      return __Z/* EXTERNAL */;
    case 7:
      var _10T/* sc2g */ = new T(function(){
        return new T3(7,_10x/* sc0h */,_10U/* sc2h */,_10u/* sc0e */);
      }),
      _10U/* sc2h */ = new T(function(){
        return B(_pa/* Data.Maybe.catMaybes1 */(B(_8G/* GHC.Base.map */(function(_10Q/* B1 */){
          return new F(function(){return _10t/* FormEngine.FormElement.FormElement.makeElem */(_10T/* sc2g */, _10v/* sc0f */, _10Q/* B1 */);});
        }, _10x/* sc0h */.c))));
      });
      return new T1(1,_10T/* sc2g */);
    case 8:
      var _10V/* sc2o */ = new T(function(){
        return new T4(8,_10x/* sc0h */,new T(function(){
          return B(_10c/* FormEngine.FormData.isCheckboxChecked */(_10x/* sc0h */, _10v/* sc0f */));
        }),_10W/* sc2p */,_10u/* sc0e */);
      }),
      _10W/* sc2p */ = new T(function(){
        return B(_pa/* Data.Maybe.catMaybes1 */(B(_8G/* GHC.Base.map */(function(_10Q/* B1 */){
          return new F(function(){return _10t/* FormEngine.FormElement.FormElement.makeElem */(_10V/* sc2o */, _10v/* sc0f */, _10Q/* B1 */);});
        }, _10x/* sc0h */.c))));
      });
      return new T1(1,_10V/* sc2o */);
    case 9:
      var _10X/* sc2v */ = new T(function(){
        return new T3(9,_10x/* sc0h */,_10Y/* sc2w */,_10u/* sc0e */);
      }),
      _10Y/* sc2w */ = new T(function(){
        return B(_pa/* Data.Maybe.catMaybes1 */(B(_8G/* GHC.Base.map */(function(_10Q/* B1 */){
          return new F(function(){return _10t/* FormEngine.FormElement.FormElement.makeElem */(_10X/* sc2v */, _10v/* sc0f */, _10Q/* B1 */);});
        }, _10x/* sc0h */.c))));
      });
      return new T1(1,_10X/* sc2v */);
    case 10:
      return new T1(1,new T2(10,_10x/* sc0h */,_10u/* sc0e */));
    default:
      return new T1(1,new T2(11,_10x/* sc0h */,_10u/* sc0e */));
  }
},
_10Z/* makeChapter */ = function(_110/* sc2D */, _111/* sc2E */){
  var _112/* sc2F */ = E(_111/* sc2E */);
  if(_112/* sc2F */._==6){
    var _113/* sc2I */ = new T(function(){
      return new T3(0,_112/* sc2F */,_114/* sc2J */,_4x/* GHC.Types.False */);
    }),
    _114/* sc2J */ = new T(function(){
      return B(_pa/* Data.Maybe.catMaybes1 */(B(_8G/* GHC.Base.map */(function(_10Q/* B1 */){
        return new F(function(){return _10t/* FormEngine.FormElement.FormElement.makeElem */(_113/* sc2I */, _110/* sc2D */, _10Q/* B1 */);});
      }, _112/* sc2F */.b))));
    });
    return new T1(1,_113/* sc2I */);
  }else{
    return __Z/* EXTERNAL */;
  }
},
_115/* main4 */ = function(_116/* B1 */){
  return new F(function(){return _10Z/* FormEngine.FormElement.FormElement.makeChapter */(_4y/* GHC.Base.Nothing */, _116/* B1 */);});
},
_117/* main_tabMaybes */ = new T(function(){
  return B(_8G/* GHC.Base.map */(_115/* Main.main4 */, _ZW/* Questionnaire.formItems */));
}),
_118/* main3 */ = new T(function(){
  return B(_pa/* Data.Maybe.catMaybes1 */(_117/* Main.main_tabMaybes */));
}),
_119/* main_go */ = function(_11a/* s8Lj */){
  while(1){
    var _11b/* s8Lk */ = E(_11a/* s8Lj */);
    if(!_11b/* s8Lk */._){
      return false;
    }else{
      if(!E(_11b/* s8Lk */.a)._){
        return true;
      }else{
        _11a/* s8Lj */ = _11b/* s8Lk */.b;
        continue;
      }
    }
  }
},
_11c/* ready_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (f) { jQuery(document).ready(f); })");
}),
_11d/* main1 */ = function(_/* EXTERNAL */){
  var _11e/* s8LI */ = __createJSFunc/* EXTERNAL */(0, function(_/* EXTERNAL */){
    var _11f/* s8Lr */ = B(_L7/* FormEngine.JQuery.selectById1 */(_L5/* Overlay.overlayId */, _/* EXTERNAL */)),
    _11g/* s8Lu */ = B(_1r/* FormEngine.JQuery.onClick1 */(_N6/* Overlay.initOverlay2 */, _11f/* s8Lr */, _/* EXTERNAL */));
    if(!B(_119/* Main.main_go */(_117/* Main.main_tabMaybes */))){
      var _11h/* s8Ly */ = B(_Mt/* Form.generateForm1 */(_118/* Main.main3 */, _/* EXTERNAL */));
      return _1p/* Haste.Prim.Any.jsNull */;
    }else{
      var _11i/* s8LB */ = B(_3/* FormEngine.JQuery.errorIO1 */(_Na/* Main.main2 */, _/* EXTERNAL */));
      return _1p/* Haste.Prim.Any.jsNull */;
    }
  }),
  _11j/* s8LO */ = __app1/* EXTERNAL */(E(_11c/* FormEngine.JQuery.ready_f1 */), _11e/* s8LI */);
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_11k/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _11d/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_11k, [0]));};window.onload = hasteMain;