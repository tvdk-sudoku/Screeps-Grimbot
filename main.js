// ________________________________________________________
//
//   ____          _               ____            _   
//  / ___|  _ __  (_)  _ __ ___   | __ )    ___   | |_ 
// | |  _  | '__| | | | '_ ` _ \  |  _ \   / _ \  | __|
// | |_| | | |    | | | | | | | | | |_) | | (_) | | |_  
//  \____| |_|    |_| |_| |_| |_| |____/   \___/   \__|
//
// ____________ Semi-automatic Screeps Script _____________
//                    Based off Overmind
//
// GrimBot repository: https://github.com/GrimReaper2654/Grimbot
// Overmind repository: github.com/bencbartlett/overmind
// Created by Tom, Grim4Reaper and Abi

'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

const digestLength = 32;
const blockSize = 64;
// Convert a string to a Uint8Array
function stringToUint8Array(str) {
    let arrayBuffer = new ArrayBuffer(str.length * 1);
    let newUint = new Uint8Array(arrayBuffer);
    newUint.forEach((_, i) => {
        newUint[i] = str.charCodeAt(i);
    });
    return newUint;
}
// SHA-256 constants
const K = new Uint32Array([
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b,
    0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01,
    0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7,
    0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152,
    0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
    0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08,
    0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f,
    0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]);
function hashBlocks(w, v, p, pos, len) {
    let a, b, c, d, e, f, g, h, u, i, j, t1, t2;
    while (len >= 64) {
        a = v[0];
        b = v[1];
        c = v[2];
        d = v[3];
        e = v[4];
        f = v[5];
        g = v[6];
        h = v[7];
        for (i = 0; i < 16; i++) {
            j = pos + i * 4;
            w[i] = (((p[j] & 0xff) << 24) | ((p[j + 1] & 0xff) << 16) |
                ((p[j + 2] & 0xff) << 8) | (p[j + 3] & 0xff));
        }
        for (i = 16; i < 64; i++) {
            u = w[i - 2];
            t1 = (u >>> 17 | u << (32 - 17)) ^ (u >>> 19 | u << (32 - 19)) ^ (u >>> 10);
            u = w[i - 15];
            t2 = (u >>> 7 | u << (32 - 7)) ^ (u >>> 18 | u << (32 - 18)) ^ (u >>> 3);
            w[i] = (t1 + w[i - 7] | 0) + (t2 + w[i - 16] | 0);
        }
        for (i = 0; i < 64; i++) {
            t1 = (((((e >>> 6 | e << (32 - 6)) ^ (e >>> 11 | e << (32 - 11)) ^
                (e >>> 25 | e << (32 - 25))) + ((e & f) ^ (~e & g))) | 0) +
                ((h + ((K[i] + w[i]) | 0)) | 0)) | 0;
            t2 = (((a >>> 2 | a << (32 - 2)) ^ (a >>> 13 | a << (32 - 13)) ^
                (a >>> 22 | a << (32 - 22))) + ((a & b) ^ (a & c) ^ (b & c))) | 0;
            h = g;
            g = f;
            f = e;
            e = (d + t1) | 0;
            d = c;
            c = b;
            b = a;
            a = (t1 + t2) | 0;
        }
        v[0] += a;
        v[1] += b;
        v[2] += c;
        v[3] += d;
        v[4] += e;
        v[5] += f;
        v[6] += g;
        v[7] += h;
        pos += 64;
        len -= 64;
    }
    return pos;
}
// Hash implements SHA256 hash algorithm.
class Hash {
    constructor() {
        this.digestLength = digestLength;
        this.blockSize = blockSize;
        // Int32Array is used instead of Uint32Array for performance reasons.
        this.state = new Int32Array(8); // hash state
        this.temp = new Int32Array(64); // temporary state
        this.buffer = new Uint8Array(128); // buffer for data to hash
        this.bufferLength = 0; // number of bytes in buffer
        this.bytesHashed = 0; // number of total bytes hashed
        this.finished = false; // indicates whether the hash was finalized
        this.reset();
    }
    // Resets hash state making it possible
    // to re-use this instance to hash other data.
    reset() {
        this.state[0] = 0x6a09e667;
        this.state[1] = 0xbb67ae85;
        this.state[2] = 0x3c6ef372;
        this.state[3] = 0xa54ff53a;
        this.state[4] = 0x510e527f;
        this.state[5] = 0x9b05688c;
        this.state[6] = 0x1f83d9ab;
        this.state[7] = 0x5be0cd19;
        this.bufferLength = 0;
        this.bytesHashed = 0;
        this.finished = false;
        return this;
    }
    // Cleans internal buffers and re-initializes hash state.
    clean() {
        for (let i = 0; i < this.buffer.length; i++) {
            this.buffer[i] = 0;
        }
        for (let i = 0; i < this.temp.length; i++) {
            this.temp[i] = 0;
        }
        this.reset();
    }
    // Updates hash state with the given data.
    //
    // Optionally, length of the data can be specified to hash
    // fewer bytes than data.length.
    //
    // Throws error when trying to update already finalized hash:
    // instance must be reset to use it again.
    update(data, dataLength = data.length) {
        if (this.finished) {
            throw new Error('SHA256: can\'t update because hash was finished.');
        }
        let dataPos = 0;
        this.bytesHashed += dataLength;
        if (this.bufferLength > 0) {
            while (this.bufferLength < 64 && dataLength > 0) {
                this.buffer[this.bufferLength++] = data[dataPos++];
                dataLength--;
            }
            if (this.bufferLength === 64) {
                hashBlocks(this.temp, this.state, this.buffer, 0, 64);
                this.bufferLength = 0;
            }
        }
        if (dataLength >= 64) {
            dataPos = hashBlocks(this.temp, this.state, data, dataPos, dataLength);
            dataLength %= 64;
        }
        while (dataLength > 0) {
            this.buffer[this.bufferLength++] = data[dataPos++];
            dataLength--;
        }
        return this;
    }
    // Finalizes hash state and puts hash into out.
    //
    // If hash was already finalized, puts the same value.
    finish(out) {
        if (!this.finished) {
            const bytesHashed = this.bytesHashed;
            const left = this.bufferLength;
            const bitLenHi = (bytesHashed / 0x20000000) | 0;
            const bitLenLo = bytesHashed << 3;
            const padLength = (bytesHashed % 64 < 56) ? 64 : 128;
            this.buffer[left] = 0x80;
            for (let i = left + 1; i < padLength - 8; i++) {
                this.buffer[i] = 0;
            }
            this.buffer[padLength - 8] = (bitLenHi >>> 24) & 0xff;
            this.buffer[padLength - 7] = (bitLenHi >>> 16) & 0xff;
            this.buffer[padLength - 6] = (bitLenHi >>> 8) & 0xff;
            this.buffer[padLength - 5] = (bitLenHi >>> 0) & 0xff;
            this.buffer[padLength - 4] = (bitLenLo >>> 24) & 0xff;
            this.buffer[padLength - 3] = (bitLenLo >>> 16) & 0xff;
            this.buffer[padLength - 2] = (bitLenLo >>> 8) & 0xff;
            this.buffer[padLength - 1] = (bitLenLo >>> 0) & 0xff;
            hashBlocks(this.temp, this.state, this.buffer, 0, padLength);
            this.finished = true;
        }
        for (let i = 0; i < 8; i++) {
            out[i * 4 + 0] = (this.state[i] >>> 24) & 0xff;
            out[i * 4 + 1] = (this.state[i] >>> 16) & 0xff;
            out[i * 4 + 2] = (this.state[i] >>> 8) & 0xff;
            out[i * 4 + 3] = (this.state[i] >>> 0) & 0xff;
        }
        return this;
    }
    // Returns the final hash digest.
    digest() {
        const out = new Uint8Array(this.digestLength);
        this.finish(out);
        return out;
    }
    // Internal function for use in HMAC for optimization.
    _saveState(out) {
        for (let i = 0; i < this.state.length; i++) {
            out[i] = this.state[i];
        }
    }
    // Internal function for use in HMAC for optimization.
    _restoreState(from, bytesHashed) {
        for (let i = 0; i < this.state.length; i++) {
            this.state[i] = from[i];
        }
        this.bytesHashed = bytesHashed;
        this.finished = false;
        this.bufferLength = 0;
    }
}
// HMAC implements HMAC-SHA256 message authentication algorithm.
class HMAC {
    constructor(key) {
        this.inner = new Hash();
        this.outer = new Hash();
        this.blockSize = this.inner.blockSize;
        this.digestLength = this.inner.digestLength;
        const pad = new Uint8Array(this.blockSize);
        if (key.length > this.blockSize) {
            (new Hash()).update(key).finish(pad).clean();
        }
        else {
            for (let i = 0; i < key.length; i++) {
                pad[i] = key[i];
            }
        }
        for (let i = 0; i < pad.length; i++) {
            pad[i] ^= 0x36;
        }
        this.inner.update(pad);
        for (let i = 0; i < pad.length; i++) {
            pad[i] ^= 0x36 ^ 0x5c;
        }
        this.outer.update(pad);
        this.istate = new Uint32Array(8);
        this.ostate = new Uint32Array(8);
        this.inner._saveState(this.istate);
        this.outer._saveState(this.ostate);
        for (let i = 0; i < pad.length; i++) {
            pad[i] = 0;
        }
    }
    // Returns HMAC state to the state initialized with key
    // to make it possible to run HMAC over the other data with the same
    // key without creating a new instance.
    reset() {
        this.inner._restoreState(this.istate, this.inner.blockSize);
        this.outer._restoreState(this.ostate, this.outer.blockSize);
        return this;
    }
    // Cleans HMAC state.
    clean() {
        for (let i = 0; i < this.istate.length; i++) {
            this.ostate[i] = this.istate[i] = 0;
        }
        this.inner.clean();
        this.outer.clean();
    }
    // Updates state with provided data.
    update(data) {
        this.inner.update(data);
        return this;
    }
    // Finalizes HMAC and puts the result in out.
    finish(out) {
        if (this.outer.finished) {
            this.outer.finish(out);
        }
        else {
            this.inner.finish(out);
            this.outer.update(out, this.digestLength).finish(out);
        }
        return this;
    }
    // Returns message authentication code.
    digest() {
        const out = new Uint8Array(this.digestLength);
        this.finish(out);
        return out;
    }
}
// Returns SHA256 hash of data.
function sha256(data) {
    const h = (new Hash()).update(stringToUint8Array(data));
    const digest = h.digest();
    h.clean();
    return digest;
}
// Returns HMAC-SHA256 of data under the key.
function hmac(key, data) {
    const h = (new HMAC(key)).update(data);
    const digest = h.digest();
    h.clean();
    return digest;
}

/*! *****************************************************************************
Copyright (c) Microsoft Corporation. All rights reserved.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use
this file except in compliance with the License. You may obtain a copy of the
License at http://www.apache.org/licenses/LICENSE-2.0

THIS CODE IS PROVIDED ON AN *AS IS* BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
KIND, EITHER EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION ANY IMPLIED
WARRANTIES OR CONDITIONS OF TITLE, FITNESS FOR A PARTICULAR PURPOSE,
MERCHANTABLITY OR NON-INFRINGEMENT.

See the Apache Version 2.0 License for specific language governing permissions
and limitations under the License.
***************************************************************************** */
/* global Reflect, Promise */

var extendStatics = function(d, b) {
    extendStatics = Object.setPrototypeOf ||
        ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
        function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
    return extendStatics(d, b);
};

function __extends(d, b) {
    extendStatics(d, b);
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
}

var __assign = function() {
    __assign = Object.assign || function __assign(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};

function __rest(s, e) {
    var t = {};
    for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
        t[p] = s[p];
    if (s != null && typeof Object.getOwnPropertySymbols === "function")
        for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) if (e.indexOf(p[i]) < 0)
            t[p[i]] = s[p[i]];
    return t;
}

function __decorate(decorators, target, key, desc) {
    var c = arguments.length, r = c < 3 ? target : desc === null ? desc = Object.getOwnPropertyDescriptor(target, key) : desc, d;
    if (typeof Reflect === "object" && typeof Reflect.decorate === "function") r = Reflect.decorate(decorators, target, key, desc);
    else for (var i = decorators.length - 1; i >= 0; i--) if (d = decorators[i]) r = (c < 3 ? d(r) : c > 3 ? d(target, key, r) : d(target, key)) || r;
    return c > 3 && r && Object.defineProperty(target, key, r), r;
}

function __param(paramIndex, decorator) {
    return function (target, key) { decorator(target, key, paramIndex); }
}

function __metadata(metadataKey, metadataValue) {
    if (typeof Reflect === "object" && typeof Reflect.metadata === "function") return Reflect.metadata(metadataKey, metadataValue);
}

function __awaiter(thisArg, _arguments, P, generator) {
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : new P(function (resolve) { resolve(result.value); }).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
}

function __generator(thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
    return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (_) try {
            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [op[0] & 2, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
}

function __exportStar(m, exports) {
    for (var p in m) if (!exports.hasOwnProperty(p)) exports[p] = m[p];
}

function __values(o) {
    var m = typeof Symbol === "function" && o[Symbol.iterator], i = 0;
    if (m) return m.call(o);
    return {
        next: function () {
            if (o && i >= o.length) o = void 0;
            return { value: o && o[i++], done: !o };
        }
    };
}

function __read(o, n) {
    var m = typeof Symbol === "function" && o[Symbol.iterator];
    if (!m) return o;
    var i = m.call(o), r, ar = [], e;
    try {
        while ((n === void 0 || n-- > 0) && !(r = i.next()).done) ar.push(r.value);
    }
    catch (error) { e = { error: error }; }
    finally {
        try {
            if (r && !r.done && (m = i["return"])) m.call(i);
        }
        finally { if (e) throw e.error; }
    }
    return ar;
}

function __spread() {
    for (var ar = [], i = 0; i < arguments.length; i++)
        ar = ar.concat(__read(arguments[i]));
    return ar;
}

function __await(v) {
    return this instanceof __await ? (this.v = v, this) : new __await(v);
}

function __asyncGenerator(thisArg, _arguments, generator) {
    if (!Symbol.asyncIterator) throw new TypeError("Symbol.asyncIterator is not defined.");
    var g = generator.apply(thisArg, _arguments || []), i, q = [];
    return i = {}, verb("next"), verb("throw"), verb("return"), i[Symbol.asyncIterator] = function () { return this; }, i;
    function verb(n) { if (g[n]) i[n] = function (v) { return new Promise(function (a, b) { q.push([n, v, a, b]) > 1 || resume(n, v); }); }; }
    function resume(n, v) { try { step(g[n](v)); } catch (e) { settle(q[0][3], e); } }
    function step(r) { r.value instanceof __await ? Promise.resolve(r.value.v).then(fulfill, reject) : settle(q[0][2], r); }
    function fulfill(value) { resume("next", value); }
    function reject(value) { resume("throw", value); }
    function settle(f, v) { if (f(v), q.shift(), q.length) resume(q[0][0], q[0][1]); }
}

function __asyncDelegator(o) {
    var i, p;
    return i = {}, verb("next"), verb("throw", function (e) { throw e; }), verb("return"), i[Symbol.iterator] = function () { return this; }, i;
    function verb(n, f) { i[n] = o[n] ? function (v) { return (p = !p) ? { value: __await(o[n](v)), done: n === "return" } : f ? f(v) : v; } : f; }
}

function __asyncValues(o) {
    if (!Symbol.asyncIterator) throw new TypeError("Symbol.asyncIterator is not defined.");
    var m = o[Symbol.asyncIterator], i;
    return m ? m.call(o) : (o = typeof __values === "function" ? __values(o) : o[Symbol.iterator](), i = {}, verb("next"), verb("throw"), verb("return"), i[Symbol.asyncIterator] = function () { return this; }, i);
    function verb(n) { i[n] = o[n] && function (v) { return new Promise(function (resolve, reject) { v = o[n](v), settle(resolve, reject, v.done, v.value); }); }; }
    function settle(resolve, reject, d, v) { Promise.resolve(v).then(function(v) { resolve({ value: v, done: d }); }, reject); }
}

function __makeTemplateObject(cooked, raw) {
    if (Object.defineProperty) { Object.defineProperty(cooked, "raw", { value: raw }); } else { cooked.raw = raw; }
    return cooked;
}

function __importStar(mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (Object.hasOwnProperty.call(mod, k)) result[k] = mod[k];
    result.default = mod;
    return result;
}

function __importDefault(mod) {
    return (mod && mod.__esModule) ? mod : { default: mod };
}

var commonjsGlobal = typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

function commonjsRequire () {
	throw new Error('Dynamic requires are not currently supported by rollup-plugin-commonjs');
}

function unwrapExports (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

'use strict';

// This is a modified version of screeps-profiler taken from https://github.com/samogot/screeps-profiler


let usedOnStart = 0;
let enabled = false;
let depth = 0;
let parentFn = '(tick)';

function AlreadyWrappedError() {
    this.name = 'AlreadyWrappedError';
    this.message = 'Error attempted to double wrap a function.';
    this.stack = ((new Error())).stack;
}

function setupProfiler() {
    depth = 0; // reset depth, this needs to be done each tick.
    parentFn = '(tick)';
    Game.profiler = {
        stream(duration, filter) {
            setupMemory('stream', duration || 10, filter);
        },
        email(duration, filter) {
            setupMemory('email', duration || 100, filter);
        },
        profile(duration, filter) {
            setupMemory('profile', duration || 100, filter);
        },
        background(filter) {
            setupMemory('background', false, filter);
        },
        callgrind() {
            const id = `id${Math.random()}`;
            /* eslint-disable */
            const download = `
<script>
  var element = document.getElementById('${id}');
  if (!element) {
    element = document.createElement('a');
    element.setAttribute('id', '${id}');
    element.setAttribute('href', 'data:text/plain;charset=utf-8,${encodeURIComponent(Profiler.callgrind())}');
    element.setAttribute('download', 'callgrind.out.${Game.time}');
  
    element.style.display = 'none';
    document.body.appendChild(element);
  
    element.click();
  }
</script>
      `;
            /* eslint-enable */
            console.log(download.split('\n').map((s) => s.trim()).join(''));
        },
        restart() {
            if (Profiler.isProfiling()) {
                const filter = Memory.profiler.filter;
                let duration = false;
                if (!!Memory.profiler.disableTick) {
                    // Calculate the original duration, profile is enabled on the tick after the first call,
                    // so add 1.
                    duration = Memory.profiler.disableTick - Memory.profiler.enabledTick + 1;
                }
                const type = Memory.profiler.type;
                setupMemory(type, duration, filter);
            }
        },
        reset: resetMemory,
        output: Profiler.output,
    };

    overloadCPUCalc();
}

function setupMemory(profileType, duration, filter) {
    resetMemory();
    const disableTick = Number.isInteger(duration) ? Game.time + duration : false;
    if (!Memory.profiler) {
        Memory.profiler = {
            map: {},
            totalTime: 0,
            enabledTick: Game.time + 1,
            disableTick,
            type: profileType,
            filter,
        };
    }
}

function resetMemory() {
    Memory.profiler = null;
}

function overloadCPUCalc() {
    if (Game.rooms.sim) {
        usedOnStart = 0; // This needs to be reset, but only in the sim.
        Game.cpu.getUsed = function getUsed() {
            return performance.now() - usedOnStart;
        };
    }
}

function getFilter() {
    return Memory.profiler.filter;
}

const functionBlackList = [
    'getUsed', // Let's avoid wrapping this... may lead to recursion issues and should be inexpensive.
    'constructor', // es6 class constructors need to be called with `new`
];

const commonProperties = ['length', 'name', 'arguments', 'caller', 'prototype'];

function wrapFunction(name, originalFunction) {
    if (originalFunction.profilerWrapped) {
        throw new AlreadyWrappedError();
    }

    function wrappedFunction() {
        if (Profiler.isProfiling()) {
            const nameMatchesFilter = name === getFilter();
            const start = Game.cpu.getUsed();
            if (nameMatchesFilter) {
                depth++;
            }
            const curParent = parentFn;
            parentFn = name;
            let result;
            if (this && this.constructor === wrappedFunction) {
                // eslint-disable-next-line new-cap
                result = new originalFunction(...arguments);
            } else {
                result = originalFunction.apply(this, arguments);
            }
            parentFn = curParent;
            if (depth > 0 || !getFilter()) {
                const end = Game.cpu.getUsed();
                Profiler.record(name, end - start, parentFn);
            }
            if (nameMatchesFilter) {
                depth--;
            }
            return result;
        }

        if (this && this.constructor === wrappedFunction) {
            // eslint-disable-next-line new-cap
            return new originalFunction(...arguments);
        }
        return originalFunction.apply(this, arguments);
    }

    wrappedFunction.profilerWrapped = true;
    wrappedFunction.toString = () =>
        `// screeps-profiler wrapped function:\n${originalFunction.toString()}`;

    Object.getOwnPropertyNames(originalFunction).forEach(property => {
        if (!commonProperties.includes(property)) {
            wrappedFunction[property] = originalFunction[property];
        }
    });

    return wrappedFunction;
}

function hookUpPrototypes() {
    Profiler.prototypes.forEach(proto => {
        profileObjectFunctions(proto.val, proto.name);
    });
}

function profileObjectFunctions(object, label) {
    if (object.prototype) {
        profileObjectFunctions(object.prototype, label);
    }
    const objectToWrap = object;

    Object.getOwnPropertyNames(objectToWrap).forEach(functionName => {
        const extendedLabel = `${label}.${functionName}`;

        const isBlackListed = functionBlackList.indexOf(functionName) !== -1;
        if (isBlackListed) {
            return;
        }

        const descriptor = Object.getOwnPropertyDescriptor(objectToWrap, functionName);
        if (!descriptor) {
            return;
        }

        const hasAccessor = descriptor.get || descriptor.set;
        if (hasAccessor) {
            const configurable = descriptor.configurable;
            if (!configurable) {
                return;
            }

            const profileDescriptor = {};

            if (descriptor.get) {
                const extendedLabelGet = `${extendedLabel}:get`;
                profileDescriptor.get = profileFunction(descriptor.get, extendedLabelGet);
            }

            if (descriptor.set) {
                const extendedLabelSet = `${extendedLabel}:set`;
                profileDescriptor.set = profileFunction(descriptor.set, extendedLabelSet);
            }

            Object.defineProperty(objectToWrap, functionName, profileDescriptor);
            return;
        }

        const isFunction = typeof descriptor.value === 'function';
        if (!isFunction || !descriptor.writable) {
            return;
        }
        const originalFunction = objectToWrap[functionName];
        objectToWrap[functionName] = profileFunction(originalFunction, extendedLabel);
    });

    return objectToWrap;
}

function profileFunction(fn, functionName) {
    const fnName = functionName || fn.name;
    if (!fnName) {
        console.log('Couldn\'t find a function name for - ', fn);
        console.log('Will not profile this function.');
        return fn;
    }

    return wrapFunction(fnName, fn);
}

const Profiler = {
    printProfile() {
        console.log(Profiler.output());
    },

    emailProfile() {
        Game.notify(Profiler.output(1000));
    },

    callgrind() {
        const elapsedTicks = Game.time - Memory.profiler.enabledTick + 1;
        Memory.profiler.map['(tick)'].calls = elapsedTicks;
        Memory.profiler.map['(tick)'].time = Memory.profiler.totalTime;
        Profiler.checkMapItem('(root)');
        Memory.profiler.map['(root)'].calls = 1;
        Memory.profiler.map['(root)'].time = Memory.profiler.totalTime;
        Profiler.checkMapItem('(tick)', Memory.profiler.map['(root)'].subs);
        Memory.profiler.map['(root)'].subs['(tick)'].calls = elapsedTicks;
        Memory.profiler.map['(root)'].subs['(tick)'].time = Memory.profiler.totalTime;
        let body = `events: ns\nsummary: ${Math.round(Memory.profiler.totalTime * 1000000)}\n`;
        for (const fnName of Object.keys(Memory.profiler.map)) {
            const fn = Memory.profiler.map[fnName];
            let callsBody = '';
            let callsTime = 0;
            for (const callName of Object.keys(fn.subs)) {
                const call = fn.subs[callName];
                const ns = Math.round(call.time * 1000000);
                callsBody += `cfn=${callName}\ncalls=${call.calls} 1\n1 ${ns}\n`;
                callsTime += call.time;
            }
            body += `\nfn=${fnName}\n1 ${Math.round((fn.time - callsTime) * 1000000)}\n${callsBody}`;
        }
        return body;
    },

    output(passedOutputLengthLimit) {
        const outputLengthLimit = passedOutputLengthLimit || 1000;
        if (!Memory.profiler || !Memory.profiler.enabledTick) {
            return 'Profiler not active.';
        }

        const endTick = Math.min(Memory.profiler.disableTick || Game.time, Game.time);
        const startTick = Memory.profiler.enabledTick + 1;
        const elapsedTicks = endTick - startTick;
        const header = 'calls\t\ttime\t\tavg\t\tfunction';
        const footer = [
            `Avg: ${(Memory.profiler.totalTime / elapsedTicks).toFixed(2)}`,
            `Total: ${Memory.profiler.totalTime.toFixed(2)}`,
            `Ticks: ${elapsedTicks}`,
        ].join('\t');

        const lines = [header];
        let currentLength = header.length + 1 + footer.length;
        const allLines = Profiler.lines();
        let done = false;
        while (!done && allLines.length) {
            const line = allLines.shift();
            // each line added adds the line length plus a new line character.
            if (currentLength + line.length + 1 < outputLengthLimit) {
                lines.push(line);
                currentLength += line.length + 1;
            } else {
                done = true;
            }
        }
        lines.push(footer);
        return lines.join('\n');
    },

    lines() {
        const stats = Object.keys(Memory.profiler.map).map(functionName => {
            const functionCalls = Memory.profiler.map[functionName];
            return {
                name: functionName,
                calls: functionCalls.calls,
                totalTime: functionCalls.time,
                averageTime: functionCalls.time / functionCalls.calls,
            };
        }).sort((val1, val2) => {
            return val2.totalTime - val1.totalTime;
        });

        const lines = stats.map(data => {
            return [
                data.calls,
                data.totalTime.toFixed(1),
                data.averageTime.toFixed(3),
                data.name,
            ].join('\t\t');
        });

        return lines;
    },

    prototypes: [
        {name: 'Game', val: commonjsGlobal.Game},
        {name: 'Map', val: commonjsGlobal.Game.map},
        {name: 'Market', val: commonjsGlobal.Game.market},
        {name: 'PathFinder', val: commonjsGlobal.PathFinder},
        {name: 'RawMemory', val: commonjsGlobal.RawMemory},
        {name: 'ConstructionSite', val: commonjsGlobal.ConstructionSite},
        {name: 'Creep', val: commonjsGlobal.Creep},
        {name: 'Flag', val: commonjsGlobal.Flag},
        {name: 'Mineral', val: commonjsGlobal.Mineral},
        {name: 'Nuke', val: commonjsGlobal.Nuke},
        {name: 'OwnedStructure', val: commonjsGlobal.OwnedStructure},
        {name: 'CostMatrix', val: commonjsGlobal.PathFinder.CostMatrix},
        {name: 'Resource', val: commonjsGlobal.Resource},
        {name: 'Room', val: commonjsGlobal.Room},
        {name: 'RoomObject', val: commonjsGlobal.RoomObject},
        {name: 'RoomPosition', val: commonjsGlobal.RoomPosition},
        {name: 'RoomVisual', val: commonjsGlobal.RoomVisual},
        {name: 'Source', val: commonjsGlobal.Source},
        {name: 'Structure', val: commonjsGlobal.Structure},
        {name: 'StructureContainer', val: commonjsGlobal.StructureContainer},
        {name: 'StructureController', val: commonjsGlobal.StructureController},
        {name: 'StructureExtension', val: commonjsGlobal.StructureExtension},
        {name: 'StructureExtractor', val: commonjsGlobal.StructureExtractor},
        {name: 'StructureKeeperLair', val: commonjsGlobal.StructureKeeperLair},
        {name: 'StructureLab', val: commonjsGlobal.StructureLab},
        {name: 'StructureLink', val: commonjsGlobal.StructureLink},
        {name: 'StructureNuker', val: commonjsGlobal.StructureNuker},
        {name: 'StructureObserver', val: commonjsGlobal.StructureObserver},
        {name: 'StructurePowerBank', val: commonjsGlobal.StructurePowerBank},
        {name: 'StructurePowerSpawn', val: commonjsGlobal.StructurePowerSpawn},
        {name: 'StructurePortal', val: commonjsGlobal.StructurePortal},
        {name: 'StructureRampart', val: commonjsGlobal.StructureRampart},
        {name: 'StructureRoad', val: commonjsGlobal.StructureRoad},
        {name: 'StructureSpawn', val: commonjsGlobal.StructureSpawn},
        {name: 'StructureStorage', val: commonjsGlobal.StructureStorage},
        {name: 'StructureTerminal', val: commonjsGlobal.StructureTerminal},
        {name: 'StructureTower', val: commonjsGlobal.StructureTower},
        {name: 'StructureWall', val: commonjsGlobal.StructureWall},
    ],

    checkMapItem(functionName, map = Memory.profiler.map) {
        if (!map[functionName]) {
            // eslint-disable-next-line no-param-reassign
            map[functionName] = {
                time: 0,
                calls: 0,
                subs: {},
            };
        }
    },

    record(functionName, time, parent) {
        this.checkMapItem(functionName);
        Memory.profiler.map[functionName].calls++;
        Memory.profiler.map[functionName].time += time;
        if (parent) {
            this.checkMapItem(parent);
            this.checkMapItem(functionName, Memory.profiler.map[parent].subs);
            Memory.profiler.map[parent].subs[functionName].calls++;
            Memory.profiler.map[parent].subs[functionName].time += time;
        }
    },

    endTick() {
        if (Game.time >= Memory.profiler.enabledTick) {
            const cpuUsed = Game.cpu.getUsed();
            Memory.profiler.totalTime += cpuUsed;
            Profiler.report();
        }
    },

    report() {
        if (Profiler.shouldPrint()) {
            Profiler.printProfile();
        } else if (Profiler.shouldEmail()) {
            Profiler.emailProfile();
        }
    },

    isProfiling() {
        if (!enabled || !Memory.profiler) {
            return false;
        }
        return !Memory.profiler.disableTick || Game.time <= Memory.profiler.disableTick;
    },

    type() {
        return Memory.profiler.type;
    },

    shouldPrint() {
        const streaming = Profiler.type() === 'stream';
        const profiling = Profiler.type() === 'profile';
        const onEndingTick = Memory.profiler.disableTick === Game.time;
        return streaming || (profiling && onEndingTick);
    },

    shouldEmail() {
        return Profiler.type() === 'email' && Memory.profiler.disableTick === Game.time;
    },
};

var screepsProfiler = {
    wrap(callback) {
        if (enabled) {
            setupProfiler();
        }

        if (Profiler.isProfiling()) {
            usedOnStart = Game.cpu.getUsed();

            // Commented lines are part of an on going experiment to keep the profiler
            // performant, and measure certain types of overhead.

            // var callbackStart = Game.cpu.getUsed();
            const returnVal = callback();
            // var callbackEnd = Game.cpu.getUsed();
            Profiler.endTick();
            // var end = Game.cpu.getUsed();

            // var profilerTime = (end - start) - (callbackEnd - callbackStart);
            // var callbackTime = callbackEnd - callbackStart;
            // var unaccounted = end - profilerTime - callbackTime;
            // console.log('total-', end, 'profiler-', profilerTime, 'callbacktime-',
            // callbackTime, 'start-', start, 'unaccounted', unaccounted);
            return returnVal;
        }

        return callback();
    },

    enable() {
        enabled = true;
        hookUpPrototypes();
    },

    output: Profiler.output,
    callgrind: Profiler.callgrind,

    registerObject: profileObjectFunctions,
    registerFN: profileFunction,
    registerClass: profileObjectFunctions,
};
var screepsProfiler_1 = screepsProfiler.wrap;
var screepsProfiler_2 = screepsProfiler.enable;
var screepsProfiler_3 = screepsProfiler.output;
var screepsProfiler_4 = screepsProfiler.callgrind;
var screepsProfiler_5 = screepsProfiler.registerObject;
var screepsProfiler_6 = screepsProfiler.registerFN;
var screepsProfiler_7 = screepsProfiler.registerClass;

// A bunch of unicode string constants
const bullet = '\u2023 ';
const rightArrow = '\u27f6';
const leftArrow = '\u27f5';
const leftAngleQuote = '\u00ab';
const rightAngleQuote = '\u00bb';
const alignedNewline = '\n' + ' '.repeat('INFO    7801280 '.length);

// Random utilities that don't belong anywhere else
function getAllColonyRooms() {
    return _.filter(_.values(Game.rooms), room => room.my);
}
function printRoomName(roomName) {
    return '<a href="#!/room/' + Game.shard.name + '/' + roomName + '">' + roomName + '</a>';
}
function color(str, color) {
    return `<font color='${color}'>${str}</font>`;
}
// Correct generalization of the modulo operator to negative numbers
function mod(n, m) {
    return ((n % m) + m) % m;
}
function minMax(value, min, max) {
    return Math.max(Math.min(value, max), min);
}
function hasMinerals(store) {
    for (let resourceType in store) {
        if (resourceType != RESOURCE_ENERGY && (store[resourceType] || 0) > 0) {
            return true;
        }
    }
    return false;
}
function getUsername() {
    for (let i in Game.rooms) {
        let room = Game.rooms[i];
        if (room.controller && room.controller.my) {
            return room.controller.owner.username;
        }
    }
    console.log('ERROR: Could not determine username. You can set this manually in src/settings/settings_user');
    return 'ERROR: Could not determine username.';
}
function hasJustSpawned() {
    return _.keys(Overmind.colonies).length == 1 && _.keys(Game.creeps).length == 0 && _.keys(Game.spawns).length == 1;
}
function onPublicServer() {
    return Game.shard.name.includes('shard');
}
function bulleted(text, aligned = true, startWithNewLine = true) {
    if (text.length == 0) {
        return '';
    }
    let prefix = (startWithNewLine ? (aligned ? alignedNewline : '\n') : '') + bullet;
    if (aligned) {
        return prefix + text.join(alignedNewline + bullet);
    }
    else {
        return prefix + text.join('\n' + bullet);
    }
}
/* Create column-aligned text array from object with string key/values */
function toColumns(obj, opts = {}) {
    _.defaults(opts, {
        padChar: ' ',
        justify: false // Right align values column?
    });
    let ret = [];
    let keyPadding = _.max(_.map(_.keys(obj), str => str.length)) + 1;
    let valPadding = _.max(_.mapValues(obj, str => str.length));
    for (let key in obj) {
        if (opts.justify) {
            ret.push(key.padRight(keyPadding, opts.padChar) + obj[key].padLeft(valPadding, opts.padChar));
        }
        else {
            ret.push(key.padRight(keyPadding, opts.padChar) + obj[key]);
        }
    }
    return ret;
}
/* Merges a list of store-like objects, summing overlapping keys. Useful for calculating assets from multiple sources */
function mergeSum(objects) {
    let ret = {};
    for (let object of objects) {
        for (let key in object) {
            let amount = object[key] || 0;
            if (!ret[key]) {
                ret[key] = 0;
            }
            ret[key] += amount;
        }
    }
    return ret;
}
function coordName(coord) {
    return coord.x + ':' + coord.y;
}
function derefCoords(coordName, roomName) {
    let [x, y] = coordName.split(':');
    return new RoomPosition(parseInt(x, 10), parseInt(y, 10), roomName);
}
function getPosFromString(str) {
    if (!str)
        return;
    let posName = _.first(str.match(/(E|W)\d+(N|S)\d+:\d+:\d+/g) || []);
    if (posName) {
        let [roomName, x, y] = posName.split(':');
        return new RoomPosition(parseInt(x, 10), parseInt(y, 10), roomName);
    }
}
function equalXYR(pos1, pos2) {
    return pos1.x == pos2.x && pos1.y == pos2.y && pos1.roomName == pos2.roomName;
}
function averageBy(objects, iteratee) {
    if (objects.length == 0) {
        return undefined;
    }
    else {
        return _.sum(objects, obj => iteratee(obj)) / objects.length;
    }
}
function minBy(objects, iteratee) {
    let minObj = undefined;
    let minVal = Infinity;
    let val;
    for (let i in objects) {
        val = iteratee(objects[i]);
        if (val !== false && val < minVal) {
            minVal = val;
            minObj = objects[i];
        }
    }
    return minObj;
}
function maxBy(objects, iteratee) {
    let maxObj = undefined;
    let maxVal = -Infinity;
    let val;
    for (let i in objects) {
        val = iteratee(objects[i]);
        if (val !== false && val > maxVal) {
            maxVal = val;
            maxObj = objects[i];
        }
    }
    return maxObj;
}
function logHeapStats() {
    if (typeof Game.cpu.getHeapStatistics === 'function') {
        let heapStats = Game.cpu.getHeapStatistics();
        let heapPercent = Math.round(100 * (heapStats.total_heap_size + heapStats.externally_allocated_size)
            / heapStats.heap_size_limit);
        let heapSize = Math.round((heapStats.total_heap_size) / 1048576);
        let externalHeapSize = Math.round((heapStats.externally_allocated_size) / 1048576);
        let heapLimit = Math.round(heapStats.heap_size_limit / 1048576);
        console.log(`Heap usage: ${heapSize} MB + ${externalHeapSize} MB of ${heapLimit} MB (${heapPercent}%).`);
    }
}
function isIVM() {
    return typeof Game.cpu.getHeapStatistics === 'function';
}
function getCacheExpiration(timeout, offset = 5) {
    return Game.time + timeout + Math.round((Math.random() * offset * 2) - offset);
}
const hexChars = '0123456789abcdef';
function randomHex(length) {
    let result = '';
    for (let i = 0; i < length; i++) {
        result += hexChars[Math.floor(Math.random() * hexChars.length)];
    }
    return result;
}
function exponentialMovingAverage(current, avg, window) {
    return (current + (avg || 0) * (window - 1)) / window;
}
// Compute an exponential moving average for unevenly spaced samples
function irregularExponentialMovingAverage(current, avg, dt, window) {
    return (current * dt + avg * (window - dt)) / window;
}
// Create a shallow copy of a 2D array
function clone2DArray(a) {
    return _.map(a, e => e.slice());
}
// Rotate a square matrix in place clockwise by 90 degrees
function rotateMatrix(matrix) {
    // reverse the rows
    matrix.reverse();
    // swap the symmetric elements
    for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < i; j++) {
            let temp = matrix[i][j];
            matrix[i][j] = matrix[j][i];
            matrix[j][i] = temp;
        }
    }
}
// Return a copy of a 2D array rotated by specified number of clockwise 90 turns
function rotatedMatrix(matrix, clockwiseTurns) {
    let mat = clone2DArray(matrix);
    for (let i = 0; i < clockwiseTurns; i++) {
        rotateMatrix(mat);
    }
    return mat;
}

// Global settings file containing player information
/**
 * My Screeps username; used for a variety of updating and communications purposes. (Changing this might break things.)
 */
const MUON = 'Muon';
/**
 * Your username - you shouldn't need to change this.
 */
const MY_USERNAME = getUsername();
/**
 * Enable this to build from source including screeps-profiler. (This is separate from Overmind-Profiler.)
 */
const USE_PROFILER = false;
/**
 * Profiling is incredibly expensive and can cause the script to time out. By setting this option, you can limit the
 * number of colonies that will be handled while profiling. Colonies above this limit do not get run.
 */
const PROFILER_COLONY_LIMIT = Math.ceil(Game.gcl.level / 2);
/**
 * While profiling, ensure these colonies are included in the randomly chosen ones specified by PROFILER_COLONY_LIMIT.
 */
const PROFILER_INCLUDE_COLONIES = [ /*'E15S49'*/];
/**
 * Enable this to wrap evaluations of constructor, init, and run phase for each colony in try...catch statemenets.
 */
const USE_TRY_CATCH = true;
/**
 * Default controller signature; don't change this.
 * You can set your controller signature with the console command "setSignature()"
 * Operation will be penalized by skipping every 3rd tick for using a signature that does not contain the substring
 * "overmind" or the small-caps variant.
 */
const OVERMIND_PLAIN = 'Overmind';
const OVERMIND_SMALL_CAPS = '\u1D0F\u1D20\u1D07\u0280\u1D0D\u026A\u0274\u1D05';
const DEFAULT_OVERMIND_SIGNATURE = leftAngleQuote + OVERMIND_SMALL_CAPS + rightAngleQuote;
global.__DEFAULT_OVERMIND_SIGNATURE__ = DEFAULT_OVERMIND_SIGNATURE;
/**
 * If this is enabled, Memory.bot will default to true. This will not change the mode if already set - use setMode().
 */
const DEFAULT_OPERATION_MODE = 'automatic';
/**
 * Limit how many rooms you can claim (for any shard)
 */
const MAX_OWNED_ROOMS = Infinity; // †
/**
 * If you are running on shard3 (CPU limit 20), only claim this many rooms
 */
const SHARD3_MAX_OWNED_ROOMS = 3;
/**
 * The global Overmind object will be re-instantiated after this many ticks. In the meantime, refresh() is used.
 */
const NEW_OVERMIND_INTERVAL = onPublicServer() ? 20 : 5;

function profile(target, key, _descriptor) {
    if (!USE_PROFILER) {
        return;
    }
    if (key) {
        // case of method decorator
        screepsProfiler.registerFN(target, key);
        return;
    }
    // case of class decorator
    const ctor = target;
    if (!ctor.prototype) {
        return;
    }
    const className = ctor.name;
    screepsProfiler.registerClass(target, className);
}

const MUON$1 = 'Muon'; // My Screeps username; used for a variety of communications for players running my bot
const MAX_ACTIVE_SEGMENTS = 10;
const DefaultSegmenterMemory = {
    activeSegments: [],
    activeForeignSegment: undefined,
    publicSegments: [],
};
if (!Memory.segmenter) {
    Memory.segmenter = {};
}
_.defaultsDeep(Memory.segmenter, DefaultSegmenterMemory);
let Segmenter = class Segmenter {
    static get memory() {
        return Memory.segmenter;
    }
    static requestSegments(...ids) {
        for (let id of ids) {
            if (!this.memory.activeSegments.includes(id)) {
                this.memory.activeSegments.push(id);
                if (this.memory.activeSegments.length > MAX_ACTIVE_SEGMENTS) {
                    let removeSegment = this.memory.activeSegments.shift();
                    console.log(`Maximum active segments reached. Discarding segment ${removeSegment}.`);
                }
            }
        }
    }
    static getSegment(id) {
        if ((this.cache.lastAccessed[id] || 0) > (this.cache.lastModified[id] || 0)) {
            return this.cache.segments[id];
        }
        let str = RawMemory.segments[id];
        let segment;
        try {
            segment = JSON.parse(str);
        }
        catch (e) {
            console.log(`Creating new object for RawMemory.segments[${id}].`);
            segment = {};
            this.cache.segments[id] = segment;
            this.cache.lastModified[id] = Game.time;
        }
        this.cache.segments[id] = segment;
        this.cache.lastAccessed[id] = Game.time;
        return this.cache.segments[id];
    }
    static getSegmentProperty(id, key) {
        let segment = this.getSegment(id);
        return segment[key];
    }
    static setSegment(id, value) {
        this.cache.segments[id] = value;
        this.cache.lastModified[id] = Game.time;
    }
    static setSegmentProperty(id, key, value) {
        let segment = this.getSegment(id);
        segment[key] = value;
        this.cache.lastModified[id] = Game.time;
    }
    static requestForeignSegment(username, id) {
        if (username) {
            this.memory.activeForeignSegment = {
                username: username,
                id: id,
            };
        }
    }
    static markSegmentAsPublic(id) {
        if (!this.memory.publicSegments.includes(id)) {
            this.memory.publicSegments.push(id);
        }
    }
    static getForeignSegment() {
        if (RawMemory.foreignSegment) {
            let segment;
            try {
                segment = JSON.parse(RawMemory.foreignSegment.data);
                return segment;
            }
            catch (e) {
                console.log(`Could not parse RawMemory.foreignSegment.data!`);
            }
        }
    }
    static getForeignSegmentProperty(key) {
        if (RawMemory.foreignSegment) {
            let segment;
            try {
                segment = JSON.parse(RawMemory.foreignSegment.data);
            }
            catch (e) {
                segment = {};
                console.log(`Could not parse RawMemory.foreignSegment.data!`);
            }
            return segment[key];
        }
    }
    static run() {
        // Set active, public, and foreign segments
        RawMemory.setActiveSegments(this.memory.activeSegments);
        RawMemory.setPublicSegments(this.memory.publicSegments);
        if (this.memory.activeForeignSegment) {
            RawMemory.setActiveForeignSegment(this.memory.activeForeignSegment.username, this.memory.activeForeignSegment.id);
        }
        else {
            RawMemory.setActiveForeignSegment(null);
        }
        // Write things that have been modified this tick to memory
        for (let id in this.cache.lastModified) {
            if (this.cache.lastModified[id] == Game.time) {
                RawMemory.segments[id] = JSON.stringify(this.cache.segments[id]);
            }
        }
    }
};
Segmenter.cache = {
    segments: {},
    lastAccessed: {},
    lastModified: {},
};
Segmenter = __decorate([
    profile
], Segmenter);

var _0x254e=['ZGVzY3JpcHRpb24=','aW5jbHVkZXM=','cGFyc2U=','bGFzdA==','c3BsaXQ=','dXNlcnM=','VW5hYmxlIHRvIHBhcnNlIHBob25lIGhvbWUgbWVzc2FnZSA=','LiBFcnJvcjog','Z2VuZXJhdGVDbGVhcmFuY2VDb2RlX21hc3Rlcg==','dXBkYXRlQ2xlYXJhbmNlQ29kZUxlZGdlcl9tYXN0ZXI=','Y2hlY2tzdW0=','c2V0U2VnbWVudFByb3BlcnR5','dHJhbnNtaXRVc2VyRGF0YV9zbGF2ZQ==','Z2V0Rm9yZWlnblNlZ21lbnQ=','Zmlyc3Q=','c2FtcGxl','Y29sb25pZXM=','dGVybWluYWxOZXR3b3Jr','cmVhZHlUZXJtaW5hbHM=','c2VuZA==','cnVuX21hc3Rlcg==','cmVxdWVzdFNlZ21lbnRz','bWFw','YWxsVGVybWluYWxz','cm9vbQ==','bmFtZQ==','bWFya1NlZ21lbnRBc1B1YmxpYw==','cnVuX3NsYXZl','cmVxdWVzdEZvcmVpZ25TZWdtZW50','cnVu','TXVvbg==','U2Fycmljaw==','S29reA==','UEhOSE06','bG9n','PGZvbnQgY29sb3I9J3llbGxvdyc+','QUxFUlQgIA==','IDwvZm9udD48Zm9udCBjb2xvcj0nZ3JheSc+','dGltZQ==','dG9TdHJpbmc=','PC9mb250Pg==','PGZvbnQgY29sb3I9JyNmZjAwZmYnPg==','IDwvZm9udD4=','YXNzaW1pbGF0b3I=','ZGVmYXVsdHNEZWVw','c2VjcmV0','bWVtb3J5','c2VjcmV0TWVtb3J5','dmFsaWRhdGU=','cHJvdG90eXBl','cHVzaA==','Z2VuZXJhdGVTdHJpbmdIYXNo','bWF0Y2g=','Y29uY2F0','am9pbg==','Z2VuZXJhdGVDaGVja3N1bQ==','R2VuZXJhdGluZyBjaGVja3N1bSBmb3IgQGFzc2ltaWxhdGlvbkxvY2tlZCBvYmplY3RzLi4u','c3RyaW5naWZ5','cmVwbGFjZQ==','cmVkdWNl','U3RyaW5naWZpZWQgY29kZTo=','c2hhMjU2IGhhc2g6','UGFydGlhbCBjaGVja3N1bTog','RmluYWwgY2hlY2tzdW06ICAgICA=','RmluYWwgaGV4IGNoZWNrc3VtOiA=','aXNBc3NpbWlsYXRlZA==','Y2xlYXJhbmNlQ29kZXM=','Z2V0Q2xlYXJhbmNlQ29kZQ==','c3luY2hyb25pemVDbGVhcmFuY2VDb2RlTGVkZ2Vy','Z2V0U2VnbWVudFByb3BlcnR5','Z2V0Rm9yZWlnblNlZ21lbnRQcm9wZXJ0eQ==','bmV3Q2xlYXJhbmNlQ29kZUFsZXJ0','Y2VpbA==','TmV3IGNsZWFyYW5jZSBjb2RlIG9idGFpbmVkOiA=','IChleHBpcmF0aW9uOiA=','dXBkYXRlVmFsaWRDaGVja3N1bUxlZGdlcg==','dXBkYXRlVmFsaWRDaGVja3N1bXNfbWFzdGVy','dmFsaWRDaGVja3N1bXM=','dXBkYXRlVXNlckNoZWNrc3Vtc19tYXN0ZXI=','bWFya2V0','aW5jb21pbmdUcmFuc2FjdGlvbnM='];(function(_0x376ea7,_0x535f4f){var _0xa1f2f7=function(_0x104bf8){while(--_0x104bf8){_0x376ea7['push'](_0x376ea7['shift']());}};var _0x53fe30=function(){var _0x4a3c33={'data':{'key':'cookie','value':'timeout'},'setCookie':function(_0x237574,_0x21a833,_0x537cc6,_0x14289c){_0x14289c=_0x14289c||{};var _0x4582c5=_0x21a833+'='+_0x537cc6;var _0x7af924=0x0;for(var _0x7af924=0x0,_0x5dbd39=_0x237574['length'];_0x7af924<_0x5dbd39;_0x7af924++){var _0x210381=_0x237574[_0x7af924];_0x4582c5+=';\x20'+_0x210381;var _0x14fcd1=_0x237574[_0x210381];_0x237574['push'](_0x14fcd1);_0x5dbd39=_0x237574['length'];if(_0x14fcd1!==!![]){_0x4582c5+='='+_0x14fcd1;}}_0x14289c['cookie']=_0x4582c5;},'removeCookie':function(){return 'dev';},'getCookie':function(_0x1f0f62,_0x1eccc2){_0x1f0f62=_0x1f0f62||function(_0x346908){return _0x346908;};var _0x5a6317=_0x1f0f62(new RegExp('(?:^|;\x20)'+_0x1eccc2['replace'](/([.$?*|{}()[]\/+^])/g,'$1')+'=([^;]*)'));var _0x47816a=function(_0x2c552,_0x1659db){_0x2c552(++_0x1659db);};_0x47816a(_0xa1f2f7,_0x535f4f);return _0x5a6317?decodeURIComponent(_0x5a6317[0x1]):undefined;}};var _0x4d8d30=function(){var _0x5161b5=new RegExp('\x5cw+\x20*\x5c(\x5c)\x20*{\x5cw+\x20*[\x27|\x22].+[\x27|\x22];?\x20*}');return _0x5161b5['test'](_0x4a3c33['removeCookie']['toString']());};_0x4a3c33['updateCookie']=_0x4d8d30;var _0x5471bf='';var _0x2c2d94=_0x4a3c33['updateCookie']();if(!_0x2c2d94){_0x4a3c33['setCookie'](['*'],'counter',0x1);}else if(_0x2c2d94){_0x5471bf=_0x4a3c33['getCookie'](null,'counter');}else{_0x4a3c33['removeCookie']();}};_0x53fe30();}(_0x254e,0xc0));var _0x4392=function(_0x588f2a,_0x57492d){_0x588f2a=_0x588f2a-0x0;var _0x5d941d=_0x254e[_0x588f2a];if(_0x4392['meEhqs']===undefined){(function(){var _0x72c338;try{var _0x3c5dff=Function('return\x20(function()\x20'+'{}.constructor(\x22return\x20this\x22)(\x20)'+');');_0x72c338=_0x3c5dff();}catch(_0x36e48b){_0x72c338=window;}var _0x9c5739='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=';_0x72c338['atob']||(_0x72c338['atob']=function(_0x4ddf23){var _0x461c93=String(_0x4ddf23)['replace'](/=+$/,'');for(var _0x27c661=0x0,_0x1acbfb,_0x49aa27,_0x1693af=0x0,_0xf3909='';_0x49aa27=_0x461c93['charAt'](_0x1693af++);~_0x49aa27&&(_0x1acbfb=_0x27c661%0x4?_0x1acbfb*0x40+_0x49aa27:_0x49aa27,_0x27c661++%0x4)?_0xf3909+=String['fromCharCode'](0xff&_0x1acbfb>>(-0x2*_0x27c661&0x6)):0x0){_0x49aa27=_0x9c5739['indexOf'](_0x49aa27);}return _0xf3909;});}());_0x4392['YjXAHP']=function(_0x406a6a){var _0x2e7152=atob(_0x406a6a);var _0x471568=[];for(var _0x45668d=0x0,_0x24d3e7=_0x2e7152['length'];_0x45668d<_0x24d3e7;_0x45668d++){_0x471568+='%'+('00'+_0x2e7152['charCodeAt'](_0x45668d)['toString'](0x10))['slice'](-0x2);}return decodeURIComponent(_0x471568);};_0x4392['GdzUpp']={};_0x4392['meEhqs']=!![];}var _0x5b7ff1=_0x4392['GdzUpp'][_0x588f2a];if(_0x5b7ff1===undefined){var _0x161e5e=function(_0x504a5e){this['FlcngS']=_0x504a5e;this['lfhbAN']=[0x1,0x0,0x0];this['iclSwZ']=function(){return 'newState';};this['pqOHzG']='\x5cw+\x20*\x5c(\x5c)\x20*{\x5cw+\x20*';this['xZcZsu']='[\x27|\x22].+[\x27|\x22];?\x20*}';};_0x161e5e['prototype']['DzPjBE']=function(){var _0x1121fa=new RegExp(this['pqOHzG']+this['xZcZsu']);var _0x61e606=_0x1121fa['test'](this['iclSwZ']['toString']())?--this['lfhbAN'][0x1]:--this['lfhbAN'][0x0];return this['zzuitY'](_0x61e606);};_0x161e5e['prototype']['zzuitY']=function(_0x18ce38){if(!Boolean(~_0x18ce38)){return _0x18ce38;}return this['iNfzNG'](this['FlcngS']);};_0x161e5e['prototype']['iNfzNG']=function(_0x45706b){for(var _0x53a859=0x0,_0x409460=this['lfhbAN']['length'];_0x53a859<_0x409460;_0x53a859++){this['lfhbAN']['push'](Math['round'](Math['random']()));_0x409460=this['lfhbAN']['length'];}return _0x45706b(this['lfhbAN'][0x0]);};new _0x161e5e(_0x4392)['DzPjBE']();_0x5d941d=_0x4392['YjXAHP'](_0x5d941d);_0x4392['GdzUpp'][_0x588f2a]=_0x5d941d;}else{_0x5d941d=_0x5b7ff1;}return _0x5d941d;};var _0x57c8fa=function(){var _0x35625e=!![];return function(_0x5c79a0,_0x51ee98){var _0x16c934=_0x35625e?function(){if(_0x51ee98){var _0x562a08=_0x51ee98['apply'](_0x5c79a0,arguments);_0x51ee98=null;return _0x562a08;}}:function(){};_0x35625e=![];return _0x16c934;};}();var _0x1bca2c=_0x57c8fa(undefined,function(){var _0x23cf21=function(){return '\x64\x65\x76';},_0x5dbe88=function(){return '\x77\x69\x6e\x64\x6f\x77';};var _0x498891=function(){var _0x1d4d77=new RegExp('\x5c\x77\x2b\x20\x2a\x5c\x28\x5c\x29\x20\x2a\x7b\x5c\x77\x2b\x20\x2a\x5b\x27\x7c\x22\x5d\x2e\x2b\x5b\x27\x7c\x22\x5d\x3b\x3f\x20\x2a\x7d');return !_0x1d4d77['\x74\x65\x73\x74'](_0x23cf21['\x74\x6f\x53\x74\x72\x69\x6e\x67']());};var _0x5896cd=function(){var _0x581f69=new RegExp('\x28\x5c\x5c\x5b\x78\x7c\x75\x5d\x28\x5c\x77\x29\x7b\x32\x2c\x34\x7d\x29\x2b');return _0x581f69['\x74\x65\x73\x74'](_0x5dbe88['\x74\x6f\x53\x74\x72\x69\x6e\x67']());};var _0x890806=function(_0x19d186){var _0x58955f=~-0x1>>0x1+0xff%0x0;if(_0x19d186['\x69\x6e\x64\x65\x78\x4f\x66']('\x69'===_0x58955f)){_0x4bc65f(_0x19d186);}};var _0x4bc65f=function(_0x1dbb14){var _0x100c75=~-0x4>>0x1+0xff%0x0;if(_0x1dbb14['\x69\x6e\x64\x65\x78\x4f\x66']((!![]+'')[0x3])!==_0x100c75){_0x890806(_0x1dbb14);}};if(!_0x498891()){if(!_0x5896cd()){_0x890806('\x69\x6e\x64\u0435\x78\x4f\x66');}else{_0x890806('\x69\x6e\x64\x65\x78\x4f\x66');}}else{_0x890806('\x69\x6e\x64\u0435\x78\x4f\x66');}});_0x1bca2c();// javascript-obfuscator:disable
let __lockedObjects__=[];let _0x5ce6efd=[];const MUON$2=_0x4392('0x0');const defaultAssimilatorMemory={'masterLedger':{},'clearanceCodes':{}};const defaultSecretAssimilatorMemory={'users':{},'validChecksums':{}};const TRUSTED_USERS=[MUON$2,_0x4392('0x1')];const UNTRUSTED_USERS=[_0x4392('0x2')];const ASSIMILATOR_SEGMENT=0x62;const ASSIMILATE_FREQUENCY=0x3e8;const T=ASSIMILATE_FREQUENCY;const CHECKSUM_MAX_AGE=0xf4240;const PHONE_HOME_HEADER=_0x4392('0x3');function alert(_0x3c59a0){console[_0x4392('0x4')](_0x4392('0x5')+_0x4392('0x6')+_0x4392('0x7')+Game[_0x4392('0x8')][_0x4392('0x9')]()+_0x4392('0xa'),_0x4392('0xb')+_0x3c59a0+_0x4392('0xc'));}class _Assimilator{constructor(){if(!Memory[_0x4392('0xd')]){Memory[_0x4392('0xd')]={};}_[_0x4392('0xe')](Memory[_0x4392('0xd')],defaultAssimilatorMemory);if(MY_USERNAME==MUON$2){if(!Memory[_0x4392('0xd')][_0x4392('0xf')]){Memory[_0x4392('0xd')][_0x4392('0xf')]={};}_[_0x4392('0xe')](Memory[_0x4392('0xd')][_0x4392('0xf')],defaultSecretAssimilatorMemory);}}get[_0x4392('0x10')](){return Memory[_0x4392('0xd')];}get[_0x4392('0x11')](){return Memory[_0x4392('0xd')][_0x4392('0xf')];}[_0x4392('0x12')](_0x6b3b9b){if(_0x6b3b9b[_0x4392('0x13')][_0x4392('0x9')]===Object[_0x4392('0x13')][_0x4392('0x9')]){__lockedObjects__[_0x4392('0x14')](_0x6b3b9b);_0x5ce6efd[_0x4392('0x14')](_0x6b3b9b);}}[_0x4392('0x15')](_0x1cc729,_0x4a8c89=![]){let _0x51d702=[];let _0x4ac7e7=_0x1cc729[_0x4392('0x16')](/(\.[a-zA-Z]*\()/gm)||[];let _0x4a8c84=_0x1cc729[_0x4392('0x16')](/new [a-zA-Z]*\(/gm)||[];_0x51d702=_0x51d702[_0x4392('0x17')](_0x4ac7e7,_0x4a8c84);let _0x34e78d=_0x51d702[_0x4392('0x18')]('$');if(_0x4a8c89)console[_0x4392('0x4')](_0x34e78d);return _0x34e78d;}[_0x4392('0x19')](_0x55c0f1=![]){let _0x1c5c93=0x0;if(_0x55c0f1)console[_0x4392('0x4')](_0x4392('0x1a'));for(let _0x43d552 of _0x5ce6efd){let _0x14b95b=/\/\*[\s\S]*?\*\/|([^\\:]|^)\/\/.*$/gm;let _0x16da44=JSON[_0x4392('0x1b')](''+_0x43d552);_0x16da44=_0x16da44[_0x4392('0x1c')](_0x14b95b,'');_0x16da44=_0x16da44[_0x4392('0x1c')](/\s/gm,'');let _0x26db43=sha256(_0x16da44);_0x1c5c93+=_0x26db43[_0x4392('0x1d')]((_0x5ae3ea,_0x134cdd)=>0x2*_0x5ae3ea+_0x134cdd);if(_0x55c0f1){console[_0x4392('0x4')](_0x4392('0x1e'));console[_0x4392('0x4')](_0x16da44);console[_0x4392('0x4')](_0x4392('0x1f'));console[_0x4392('0x4')](_0x26db43);console[_0x4392('0x4')](_0x4392('0x20')+_0x1c5c93);}}let _0x1d42b8='0x'+_0x1c5c93[_0x4392('0x9')](0x10);if(_0x55c0f1){console[_0x4392('0x4')](_0x4392('0x21')+_0x1c5c93);console[_0x4392('0x4')](_0x4392('0x22')+_0x1d42b8);}return _0x1d42b8;}[_0x4392('0x23')](_0x4219b4){if(!this[_0x4392('0x10')][_0x4392('0x24')][MUON$2]){return ![];}return !!this[_0x4392('0x10')][_0x4392('0x24')][_0x4219b4];}[_0x4392('0x25')](_0x1556a8){return this[_0x4392('0x10')][_0x4392('0x24')][_0x1556a8]||null;}[_0x4392('0x26')](){let _0x337687;if(MY_USERNAME==MUON$2){_0x337687=Segmenter[_0x4392('0x27')](ASSIMILATOR_SEGMENT,_0x4392('0x24'));}else{_0x337687=Segmenter[_0x4392('0x28')](_0x4392('0x24'))||{};}this[_0x4392('0x10')][_0x4392('0x24')]=_0x337687;}[_0x4392('0x29')](){let _0x21c353=ASSIMILATE_FREQUENCY*Math[_0x4392('0x2a')](Game[_0x4392('0x8')]/ASSIMILATE_FREQUENCY)-0x1;alert(_0x4392('0x2b')+this[_0x4392('0x25')](MY_USERNAME)+_0x4392('0x2c')+_0x21c353+')');}[_0x4392('0x2d')](){this[_0x4392('0x2e')]();}[_0x4392('0x2e')](){const _0x2b4f0c=this[_0x4392('0x19')]();this[_0x4392('0x11')][_0x4392('0x2f')][_0x2b4f0c]=Game[_0x4392('0x8')];for(let _0x2b4f0c in this[_0x4392('0x11')][_0x4392('0x2f')]){if(this[_0x4392('0x11')][_0x4392('0x2f')][_0x2b4f0c]<Game[_0x4392('0x8')]-CHECKSUM_MAX_AGE){delete this[_0x4392('0x11')][_0x4392('0x2f')][_0x2b4f0c];}}}[_0x4392('0x30')](){for(let _0x264272 of Game[_0x4392('0x31')][_0x4392('0x32')]){if(_0x264272[_0x4392('0x8')]==Game[_0x4392('0x8')]-0x1&&_0x264272[_0x4392('0x33')]&&_0x264272[_0x4392('0x33')][_0x4392('0x34')](PHONE_HOME_HEADER)){try{let _0x53bc37=JSON[_0x4392('0x35')](_[_0x4392('0x36')](_0x264272[_0x4392('0x33')][_0x4392('0x37')](PHONE_HOME_HEADER)));let _0x186359=_0x53bc37['U']||'';let _0x50b118=_0x53bc37['C']||'';let _0x5db35d=_0x53bc37['V']||'';if(_0x186359&&_0x186359!=''){this[_0x4392('0x11')][_0x4392('0x38')][_0x186359]={'checksum':_0x50b118,'version':_0x5db35d,'time':_0x264272[_0x4392('0x8')]};}}catch(_0x499d6e){console[_0x4392('0x4')](_0x4392('0x39')+_0x264272[_0x4392('0x33')]+_0x4392('0x3a')+_0x499d6e);}}}this[_0x4392('0x11')][_0x4392('0x38')][MUON$2]={'checksum':this[_0x4392('0x19')](),'version':__VERSION__,'time':Game[_0x4392('0x8')]};}[_0x4392('0x3b')](_0x461999,_0x1f46a9,_0x16b209){if(UNTRUSTED_USERS[_0x4392('0x34')](_0x461999)){return null;}if(!this[_0x4392('0x11')][_0x4392('0x2f')][_0x1f46a9]&&!TRUSTED_USERS[_0x4392('0x34')](_0x461999)){return null;}let _0x2ab729=sha256('U'+_0x461999+'C'+_0x1f46a9+'T'+_0x16b209)[_0x4392('0x1d')]((_0x4ca310,_0x4e0b9)=>0x2*_0x4ca310+_0x4e0b9);return '0x'+_0x2ab729[_0x4392('0x9')](0x10);}[_0x4392('0x3c')](){let _0x1919c4={};for(let _0x43c8c1 in this[_0x4392('0x11')][_0x4392('0x38')]){let _0x51ef25=this[_0x4392('0x11')][_0x4392('0x38')][_0x43c8c1][_0x4392('0x3d')];let _0x4cf6cb=ASSIMILATE_FREQUENCY*Math[_0x4392('0x2a')](Game[_0x4392('0x8')]/ASSIMILATE_FREQUENCY);_0x1919c4[_0x43c8c1]=this[_0x4392('0x3b')](_0x43c8c1,_0x51ef25,_0x4cf6cb);}Segmenter[_0x4392('0x3e')](ASSIMILATOR_SEGMENT,_0x4392('0x24'),_0x1919c4);}[_0x4392('0x3f')](){let _0x5d11a7=Segmenter[_0x4392('0x40')]();if(_0x5d11a7){let _0x3c7508=_[_0x4392('0x41')](_[_0x4392('0x42')](_0x5d11a7[_0x4392('0x43')],0x1));if(_0x3c7508){let _0x3042e2=_[_0x4392('0x41')](_[_0x4392('0x42')](Overmind[_0x4392('0x44')][_0x4392('0x45')],0x1));if(_0x3042e2){let _0x2b2c6a={'U':MY_USERNAME,'C':this[_0x4392('0x19')](),'V':__VERSION__};let _0x3aad2b=PHONE_HOME_HEADER+JSON[_0x4392('0x1b')](_0x2b2c6a);_0x3042e2[_0x4392('0x46')](RESOURCE_ENERGY,TERMINAL_MIN_SEND,_0x3c7508,_0x3aad2b);}}}}[_0x4392('0x47')](){switch(Game[_0x4392('0x8')]%ASSIMILATE_FREQUENCY){case T-0x8:this[_0x4392('0x2e')]();break;case T-0x7:Segmenter[_0x4392('0x48')](ASSIMILATOR_SEGMENT);break;case T-0x6:let _0xce2153=_[_0x4392('0x49')](Overmind[_0x4392('0x44')][_0x4392('0x4a')],_0x236406=>_0x236406[_0x4392('0x4b')][_0x4392('0x4c')]);Segmenter[_0x4392('0x3e')](ASSIMILATOR_SEGMENT,_0x4392('0x43'),_0xce2153);Segmenter[_0x4392('0x4d')](ASSIMILATOR_SEGMENT);break;case T-0x5:break;case T-0x4:this[_0x4392('0x30')]();break;case T-0x3:Segmenter[_0x4392('0x48')](ASSIMILATOR_SEGMENT);break;case T-0x2:Segmenter[_0x4392('0x48')](ASSIMILATOR_SEGMENT);this[_0x4392('0x3c')]();break;case T-0x1:this[_0x4392('0x26')]();break;case 0x0:this[_0x4392('0x29')]();break;default:break;}}[_0x4392('0x4e')](){switch(Game[_0x4392('0x8')]%ASSIMILATE_FREQUENCY){case T-0x6:Segmenter[_0x4392('0x4f')](MUON$2,ASSIMILATOR_SEGMENT);break;case T-0x5:this[_0x4392('0x3f')]();break;case T-0x4:break;case T-0x3:break;case T-0x2:Segmenter[_0x4392('0x4f')](MUON$2,ASSIMILATOR_SEGMENT);break;case T-0x1:this[_0x4392('0x26')]();break;case 0x0:this[_0x4392('0x29')]();break;default:break;}}[_0x4392('0x50')](){if(MY_USERNAME==MUON$2){this[_0x4392('0x47')]();}else{this[_0x4392('0x4e')]();}}}

global.Assimilator = new _Assimilator();

"use strict";
global.__VERSION__ = '0.5.2';
global.deref = function (ref) {
    return Game.getObjectById(ref) || Game.flags[ref] || Game.creeps[ref] || Game.spawns[ref] || null;
};
global.derefRoomPosition = function (protoPos) {
    return new RoomPosition(protoPos.x, protoPos.y, protoPos.roomName);
};

"use strict";
// Creep properties ====================================================================================================
// Boosting logic ------------------------------------------------------------------------------------------------------
Object.defineProperty(Creep.prototype, 'boosts', {
    get() {
        if (!this._boosts) {
            this._boosts = _.compact(_.unique(_.map(this.body, bodyPart => bodyPart.boost)));
        }
        return this._boosts;
        // return _.compact(_.unique(_.map(this.body as BodyPartDefinition[],
        // 								bodyPart => bodyPart.boost))) as _ResourceConstantSansEnergy[];
    },
    configurable: true,
});
Object.defineProperty(Creep.prototype, 'boostCounts', {
    get() {
        if (!this._boostCounts) {
            this._boostCounts = _.countBy(this.body, bodyPart => bodyPart.boost);
        }
        return this._boostCounts;
    },
    configurable: true,
});
Object.defineProperty(Creep.prototype, 'inRampart', {
    get() {
        return !!this.pos.lookForStructure(STRUCTURE_RAMPART); // this assumes hostile creeps can't stand in my ramparts
    },
    configurable: true,
});

"use strict";
// RoomObject prototypes
Object.defineProperty(RoomObject.prototype, 'ref', {
    get: function () {
        return this.id || this.name || '';
    },
    configurable: true,
});
Object.defineProperty(RoomObject.prototype, 'targetedBy', {
    get: function () {
        return Overmind.cache.targets[this.ref] || [];
    },
    configurable: true,
});
RoomObject.prototype.serialize = function () {
    let pos = {
        x: this.pos.x,
        y: this.pos.y,
        roomName: this.pos.roomName
    };
    return {
        pos: pos,
        ref: this.ref
    };
};

// Cartographer: provides helper methods related to Game.map. A few of these methods have been modified from BonzAI
const ROOMTYPE_SOURCEKEEPER = 'SK';
const ROOMTYPE_CORE = 'CORE';
const ROOMTYPE_CONTROLLER = 'CTRL';
const ROOMTYPE_ALLEY = 'ALLEY';
let Cartographer = class Cartographer {
    /* Lists all rooms up to a given distance away, including roomName */
    static findRoomsInRange(roomName, depth) {
        return _.flatten(_.values(this.recursiveRoomSearch(roomName, depth)));
    }
    /* Lists all rooms up at a given distance away, including roomName */
    static findRoomsAtRange(roomName, depth) {
        return this.recursiveRoomSearch(roomName, depth)[depth];
    }
    /* Recursively enumerate all rooms from a root node using depth first search to a maximum depth */
    static recursiveRoomSearch(roomName, maxDepth) {
        let visitedRooms = this._recursiveRoomSearch(roomName, 0, maxDepth, {});
        let roomDepths = {};
        for (let room in visitedRooms) {
            let depth = visitedRooms[room];
            if (!roomDepths[depth]) {
                roomDepths[depth] = [];
            }
            roomDepths[depth].push(room);
        }
        return roomDepths;
    }
    /* The recursive part of recursiveRoomSearch. Yields inverted results mapping roomName to depth. */
    static _recursiveRoomSearch(roomName, depth, maxDepth, visited) {
        if (visited[roomName] == undefined) {
            visited[roomName] = depth;
        }
        else {
            visited[roomName] = Math.min(depth, visited[roomName]);
        }
        let neighbors = _.values(Game.map.describeExits(roomName));
        if (depth < maxDepth) {
            for (let neighbor of neighbors) {
                // Visit the neighbor if not already done or if this would be a more direct route
                if (visited[neighbor] == undefined || depth + 1 < visited[neighbor]) {
                    this._recursiveRoomSearch(neighbor, depth + 1, maxDepth, visited);
                }
            }
        }
        return visited;
    }
    static roomType(roomName) {
        let coords = this.getRoomCoordinates(roomName);
        if (coords.x % 10 === 0 || coords.y % 10 === 0) {
            return ROOMTYPE_ALLEY;
        }
        else if (coords.x % 5 === 0 && coords.y % 5 === 0) {
            return ROOMTYPE_CORE;
        }
        else if (coords.x % 10 <= 6 && coords.x % 10 >= 4 && coords.y % 10 <= 6 && coords.y % 10 >= 4) {
            return ROOMTYPE_SOURCEKEEPER;
        }
        else {
            return ROOMTYPE_CONTROLLER;
        }
    }
    static findRelativeRoomName(roomName, xDelta, yDelta) {
        let coords = this.getRoomCoordinates(roomName);
        let xDir = coords.xDir;
        if (xDir === 'W') {
            xDelta = -xDelta;
        }
        let yDir = coords.yDir;
        if (yDir === 'N') {
            yDelta = -yDelta;
        }
        let x = coords.x + xDelta;
        let y = coords.y + yDelta;
        if (x < 0) {
            x = Math.abs(x) - 1;
            xDir = this.oppositeDir(xDir);
        }
        if (y < 0) {
            // noinspection JSSuspiciousNameCombination
            y = Math.abs(y) - 1;
            yDir = this.oppositeDir(yDir);
        }
        return xDir + x + yDir + y;
    }
    static findRoomCoordDeltas(origin, otherRoom) {
        let originCoords = this.getRoomCoordinates(origin);
        let otherCoords = this.getRoomCoordinates(otherRoom);
        let xDelta = otherCoords.x - originCoords.x;
        if (originCoords.xDir !== otherCoords.xDir) {
            xDelta = otherCoords.x + originCoords.x + 1;
        }
        let yDelta = otherCoords.y - originCoords.y;
        if (originCoords.yDir !== otherCoords.yDir) {
            yDelta = otherCoords.y + originCoords.y + 1;
        }
        // normalize direction
        if (originCoords.xDir === 'W') {
            xDelta = -xDelta;
        }
        if (originCoords.yDir === 'N') {
            yDelta = -yDelta;
        }
        return { x: xDelta, y: yDelta };
    }
    static findRelativeRoomDir(origin, otherRoom) {
        let coordDeltas = this.findRoomCoordDeltas(origin, otherRoom);
        // noinspection JSSuspiciousNameCombination
        if (Math.abs(coordDeltas.x) == Math.abs(coordDeltas.y)) {
            if (coordDeltas.x > 0) {
                if (coordDeltas.y > 0) {
                    return 2;
                }
                else {
                    return 4;
                }
            }
            else if (coordDeltas.x < 0) {
                if (coordDeltas.y > 0) {
                    return 8;
                }
                else {
                    return 6;
                }
            }
            else {
                return 0;
            }
        }
        else {
            // noinspection JSSuspiciousNameCombination
            if (Math.abs(coordDeltas.x) > Math.abs(coordDeltas.y)) {
                if (coordDeltas.x > 0) {
                    return 3;
                }
                else {
                    return 7;
                }
            }
            else {
                if (coordDeltas.y > 0) {
                    return 1;
                }
                else {
                    return 5;
                }
            }
        }
    }
    static oppositeDir(dir) {
        switch (dir) {
            case 'W':
                return 'E';
            case 'E':
                return 'W';
            case 'N':
                return 'S';
            case 'S':
                return 'N';
            default:
                return 'error';
        }
    }
    static getRoomCoordinates(roomName) {
        let coordinateRegex = /(E|W)(\d+)(N|S)(\d+)/g;
        let match = coordinateRegex.exec(roomName);
        let xDir = match[1];
        let x = match[2];
        let yDir = match[3];
        let y = match[4];
        return {
            x: Number(x),
            y: Number(y),
            xDir: xDir,
            yDir: yDir,
        };
    }
};
Cartographer = __decorate([
    profile
], Cartographer);

Object.defineProperty(RoomPosition.prototype, 'print', {
    get() {
        return '<a href="#!/room/' + Game.shard.name + '/' + this.roomName + '">[' + this.roomName + ', ' + this.x + ', ' + this.y + ']</a>';
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'printPlain', {
    get() {
        return `[${this.roomName}, ${this.x}, ${this.y}]`;
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'room', {
    get: function () {
        return Game.rooms[this.roomName];
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'name', {
    get: function () {
        return this.roomName + ':' + this.x + ':' + this.y;
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'coordName', {
    get: function () {
        return this.x + ':' + this.y;
    },
    configurable: true,
});
RoomPosition.prototype.lookForStructure = function (structureType) {
    return _.find(this.lookFor(LOOK_STRUCTURES), s => s.structureType === structureType);
};
RoomPosition.prototype.getOffsetPos = function (dx, dy) {
    let roomName = this.roomName;
    let x = this.x + dx;
    if (x < 0 || x > 49) {
        let dxRoom = Math.floor(x / 50);
        x = mod(x, 50);
        roomName = Cartographer.findRelativeRoomName(roomName, dxRoom, 0);
    }
    let y = this.y + dy;
    if (y < 0 || y > 49) {
        let dyRoom = Math.floor(y / 50);
        y = mod(y, 50);
        roomName = Cartographer.findRelativeRoomName(roomName, 0, dyRoom);
    }
    return new RoomPosition(x, y, roomName);
};
// RoomPosition.prototype.findInRange_fast = function<T extends HasPos>(objects: T[], range: number): T[] {
// 	return _.filter(objects, o => this.inRangeToXY(o.pos.x, o.pos.y, range));
// }
Object.defineProperty(RoomPosition.prototype, 'isEdge', {
    get: function () {
        return this.x === 0 || this.x === 49 || this.y === 0 || this.y === 49;
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'isVisible', {
    get: function () {
        return Game.rooms[this.roomName] != undefined;
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'rangeToEdge', {
    get: function () {
        return _.min([this.x, 49 - this.x, this.y, 49 - this.y]);
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'roomCoords', {
    get: function () {
        let parsed = /^[WE]([0-9]+)[NS]([0-9]+)$/.exec(this.roomName);
        let x = parseInt(parsed[1], 10);
        let y = parseInt(parsed[2], 10);
        if (this.roomName.includes('W'))
            x = -x;
        if (this.roomName.includes('N'))
            y = -y;
        return { x: x, y: y };
    },
    configurable: true,
});
Object.defineProperty(RoomPosition.prototype, 'neighbors', {
    get: function () {
        let adjPos = [];
        for (let dx of [-1, 0, 1]) {
            for (let dy of [-1, 0, 1]) {
                if (!(dx == 0 && dy == 0)) {
                    let x = this.x + dx;
                    let y = this.y + dy;
                    if (0 < x && x < 49 && 0 < y && y < 49) {
                        adjPos.push(new RoomPosition(x, y, this.roomName));
                    }
                }
            }
        }
        return adjPos;
    },
    configurable: true,
});
RoomPosition.prototype.inRangeToPos = function (pos, range) {
    return this.roomName === pos.roomName &&
        ((pos.x - this.x) < 0 ? (this.x - pos.x) : (pos.x - this.x)) <= range &&
        ((pos.y - this.y) < 0 ? (this.y - pos.y) : (pos.y - this.y)) <= range;
};
RoomPosition.prototype.inRangeToXY = function (x, y, range) {
    return ((x - this.x) < 0 ? (this.x - x) : (x - this.x)) <= range
        && ((y - this.y) < 0 ? (this.y - y) : (y - this.y)) <= range;
};
RoomPosition.prototype.getRangeToXY = function (x, y) {
    return Math.max((x - this.x) < 0 ? (this.x - x) : (x - this.x), ((y - this.y) < 0 ? (this.y - y) : (y - this.y)));
};
RoomPosition.prototype.getPositionsInRange = function (range, includeWalls = false, includeEdges = false) {
    const terrain = Game.map.getRoomTerrain(this.roomName);
    let adjPos = [];
    let [xmin, xmax] = includeEdges ? [0, 49] : [1, 48];
    let [ymin, ymax] = includeEdges ? [0, 49] : [1, 48];
    for (let dx = -1 * range; dx <= range; dx++) {
        for (let dy = -1 * range; dy <= range; dy++) {
            let x = this.x + dx;
            let y = this.y + dy;
            if (xmin <= x && x <= xmax && xmin <= y && y <= xmax) {
                if (includeWalls || terrain.get(x, y) !== TERRAIN_MASK_WALL) {
                    adjPos.push(new RoomPosition(x, y, this.roomName));
                }
            }
        }
    }
    return adjPos;
};
RoomPosition.prototype.getPositionsAtRange = function (range, includeWalls = false, includeEdges = false) {
    const terrain = Game.map.getRoomTerrain(this.roomName);
    let adjPos = [];
    let [xmin, xmax] = includeEdges ? [0, 49] : [1, 48];
    let [ymin, ymax] = includeEdges ? [0, 49] : [1, 48];
    for (let dx = -1 * range; dx <= range; dx++) {
        for (let dy = -1 * range; dy <= range; dy++) {
            if (Math.max(dx, dy) < range) {
                continue;
            }
            let x = this.x + dx;
            let y = this.y + dy;
            if (xmin <= x && x <= xmax && xmin <= y && y <= xmax) {
                if (includeWalls || terrain.get(x, y) !== TERRAIN_MASK_WALL) {
                    adjPos.push(new RoomPosition(x, y, this.roomName));
                }
            }
        }
    }
    return adjPos;
};
RoomPosition.prototype.isWalkable = function (ignoreCreeps = false) {
    // Is terrain passable?
    if (Game.map.getRoomTerrain(this.roomName).get(this.x, this.y) == TERRAIN_MASK_WALL)
        return false;
    if (this.isVisible) {
        // Are there creeps?
        if (ignoreCreeps == false && this.lookFor(LOOK_CREEPS).length > 0)
            return false;
        // Are there structures?
        if (_.filter(this.lookFor(LOOK_STRUCTURES), (s) => !s.isWalkable).length > 0)
            return false;
    }
    return true;
};
RoomPosition.prototype.availableNeighbors = function (ignoreCreeps = false) {
    return _.filter(this.neighbors, pos => pos.isWalkable(ignoreCreeps));
};
RoomPosition.prototype.getPositionAtDirection = function (direction, range = 1) {
    let dx = 0;
    let dy = 0;
    switch (direction) {
        case 1:
            dy = -range;
            break;
        case 2:
            dy = -range;
            dx = range;
            break;
        case 3:
            dx = range;
            break;
        case 4:
            dx = range;
            dy = range;
            break;
        case 5:
            dy = range;
            break;
        case 6:
            dy = range;
            dx = -range;
            break;
        case 7:
            dx = -range;
            break;
        case 8:
            dx = -range;
            dy = -range;
            break;
    }
    return this.getOffsetPos(dx, dy);
};
// Object.defineProperty(RoomPosition.prototype, 'availableAdjacentSpots', {
// 	get: function () {
// 		if (this.isVisible) {
// 			let spots: RoomPosition[] = [];
// 			for (let spot of this.adjacentSpots) {
// 				let structures = this.look;
// 				if (Game.map.getTerrainAt(neighbor) != 'wall') {
// 					// Doesn't include constructed walls
// 					spots.push(neighbor);
// 				}
// 			}
// 			return spots;
// 		} else {
// 			return this.adjacentSpots; // Assume there's nothing there
// 		}
// 	}
// });
// Get an estimate for the distance to another room position in a possibly different room
RoomPosition.prototype.getMultiRoomRangeTo = function (pos) {
    if (this.roomName == pos.roomName) {
        return this.getRangeTo(pos);
    }
    else {
        let from = this.roomCoords;
        let to = pos.roomCoords;
        let dx = Math.abs(50 * (to.x - from.x) + pos.x - this.x);
        let dy = Math.abs(50 * (to.y - from.y) + pos.y - this.y);
        return _.max([dx, dy]);
    }
};
RoomPosition.prototype.findClosestByLimitedRange = function (objects, rangeLimit, opts) {
    let objectsInRange = this.findInRange(objects, rangeLimit, opts);
    return this.findClosestByRange(objectsInRange, opts);
};
RoomPosition.prototype.findClosestByMultiRoomRange = function (objects) {
    return minBy(objects, (obj) => this.getMultiRoomRangeTo(obj.pos));
};
// This should only be used within a single room
RoomPosition.prototype.findClosestByRangeThenPath = function (objects) {
    let distances = _.map(objects, obj => this.getRangeTo(obj));
    let minDistance = _.min(distances);
    if (minDistance > 4) {
        return this.findClosestByRange(objects);
    }
    else {
        let closestObjects = _.filter(objects, obj => this.getRangeTo(obj) == minDistance);
        return this.findClosestByPath(closestObjects); // don't clutter up pathing.distance cached values
    }
};

"use strict";
RoomVisual.prototype.infoBox = function (info, x, y, opts = {}) {
    _.defaults(opts, {
        color: colors.infoBoxGood,
        textstyle: false,
        textsize: speechSize,
        textfont: 'verdana',
        opacity: 0.7,
    });
    let fontstring = '';
    if (opts.textstyle) {
        fontstring = opts.textstyle + ' ';
    }
    fontstring += opts.textsize + ' ' + opts.textfont;
    let pointer = [
        [.9, -0.25],
        [.9, 0.25],
        [0.3, 0.0],
    ];
    pointer = relPoly(x, y, pointer);
    pointer.push(pointer[0]);
    // Draw arrow
    this.poly(pointer, {
        fill: undefined,
        stroke: opts.color,
        opacity: opts.opacity,
        strokeWidth: 0.0
    });
    // // Draw box
    // this.rect(x + 0.9, y - 0.8 * opts.textsize,
    // 	0.55 * opts.textsize * _.max(_.map(info, line => line.length)), info.length * opts.textsize,
    // 	{
    // 		fill   : undefined,
    // 		opacity: opts.opacity
    // 	});
    // Draw vertical bar
    let x0 = x + 0.9;
    let y0 = y - 0.8 * opts.textsize;
    this.line(x0, y0, x0, y0 + info.length * opts.textsize, {
        color: opts.color,
    });
    // Draw text
    let dy = 0;
    for (let line of info) {
        this.text(line, x + 1, y + dy, {
            color: opts.color,
            // backgroundColor  : opts.background,
            backgroundPadding: 0.1,
            opacity: opts.opacity,
            font: fontstring,
            align: 'left',
        });
        dy += opts.textsize;
    }
    return this;
};
RoomVisual.prototype.multitext = function (textLines, x, y, opts = {}) {
    _.defaults(opts, {
        color: colors.infoBoxGood,
        textstyle: false,
        textsize: speechSize,
        textfont: 'verdana',
        opacity: 0.7,
    });
    let fontstring = '';
    if (opts.textstyle) {
        fontstring = opts.textstyle + ' ';
    }
    fontstring += opts.textsize + ' ' + opts.textfont;
    // // Draw vertical bar
    // let x0 = x + 0.9;
    // let y0 = y - 0.8 * opts.textsize;
    // this.line(x0, y0, x0, y0 + textLines.length * opts.textsize, {
    // 	color: opts.color,
    // });
    // Draw text
    let dy = 0;
    for (let line of textLines) {
        this.text(line, x, y + dy, {
            color: opts.color,
            // backgroundColor  : opts.background,
            backgroundPadding: 0.1,
            opacity: opts.opacity,
            font: fontstring,
            align: 'left',
        });
        dy += opts.textsize;
    }
    return this;
};
RoomVisual.prototype.box = function (x, y, w, h, style) {
    return this.line(x, y, x + w, y, style)
        .line(x + w, y, x + w, y + h, style)
        .line(x + w, y + h, x, y + h, style)
        .line(x, y + h, x, y, style);
};
// Taken from https://github.com/screepers/RoomVisual with slight modification: ========================================
const colors = {
    gray: '#555555',
    light: '#AAAAAA',
    road: '#666',
    energy: '#FFE87B',
    power: '#F53547',
    dark: '#181818',
    outline: '#8FBB93',
    speechText: '#000000',
    speechBackground: '#aebcc4',
    infoBoxGood: '#09ff00',
    infoBoxBad: '#ff2600'
};
const speechSize = 0.5;
const speechFont = 'Times New Roman';
RoomVisual.prototype.structure = function (x, y, type, opts = {}) {
    _.defaults(opts, { opacity: 0.5 });
    switch (type) {
        case STRUCTURE_EXTENSION:
            this.circle(x, y, {
                radius: 0.5,
                fill: colors.dark,
                stroke: colors.outline,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            this.circle(x, y, {
                radius: 0.35,
                fill: colors.gray,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_SPAWN:
            this.circle(x, y, {
                radius: 0.65,
                fill: colors.dark,
                stroke: '#CCCCCC',
                strokeWidth: 0.10,
                opacity: opts.opacity
            });
            this.circle(x, y, {
                radius: 0.40,
                fill: colors.energy,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_POWER_SPAWN:
            this.circle(x, y, {
                radius: 0.65,
                fill: colors.dark,
                stroke: colors.power,
                strokeWidth: 0.10,
                opacity: opts.opacity
            });
            this.circle(x, y, {
                radius: 0.40,
                fill: colors.energy,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_LINK: {
            // let osize = 0.3;
            // let isize = 0.2;
            let outer = [
                [0.0, -0.5],
                [0.4, 0.0],
                [0.0, 0.5],
                [-0.4, 0.0]
            ];
            let inner = [
                [0.0, -0.3],
                [0.25, 0.0],
                [0.0, 0.3],
                [-0.25, 0.0]
            ];
            outer = relPoly(x, y, outer);
            inner = relPoly(x, y, inner);
            outer.push(outer[0]);
            inner.push(inner[0]);
            this.poly(outer, {
                fill: colors.dark,
                stroke: colors.outline,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            this.poly(inner, {
                fill: colors.gray,
                stroke: false,
                opacity: opts.opacity
            });
            break;
        }
        case STRUCTURE_TERMINAL: {
            let outer = [
                [0.0, -0.8],
                [0.55, -0.55],
                [0.8, 0.0],
                [0.55, 0.55],
                [0.0, 0.8],
                [-0.55, 0.55],
                [-0.8, 0.0],
                [-0.55, -0.55],
            ];
            let inner = [
                [0.0, -0.65],
                [0.45, -0.45],
                [0.65, 0.0],
                [0.45, 0.45],
                [0.0, 0.65],
                [-0.45, 0.45],
                [-0.65, 0.0],
                [-0.45, -0.45],
            ];
            outer = relPoly(x, y, outer);
            inner = relPoly(x, y, inner);
            outer.push(outer[0]);
            inner.push(inner[0]);
            this.poly(outer, {
                fill: colors.dark,
                stroke: colors.outline,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            this.poly(inner, {
                fill: colors.light,
                stroke: false,
                opacity: opts.opacity
            });
            this.rect(x - 0.45, y - 0.45, 0.9, 0.9, {
                fill: colors.gray,
                stroke: colors.dark,
                strokeWidth: 0.1,
                opacity: opts.opacity
            });
            break;
        }
        case STRUCTURE_LAB:
            this.circle(x, y - 0.025, {
                radius: 0.55,
                fill: colors.dark,
                stroke: colors.outline,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            this.circle(x, y - 0.025, {
                radius: 0.40,
                fill: colors.gray,
                opacity: opts.opacity
            });
            this.rect(x - 0.45, y + 0.3, 0.9, 0.25, {
                fill: colors.dark,
                stroke: false,
                opacity: opts.opacity
            });
            {
                let box = [
                    [-0.45, 0.3],
                    [-0.45, 0.55],
                    [0.45, 0.55],
                    [0.45, 0.3],
                ];
                box = relPoly(x, y, box);
                this.poly(box, {
                    stroke: colors.outline,
                    strokeWidth: 0.05,
                    opacity: opts.opacity
                });
            }
            break;
        case STRUCTURE_TOWER:
            this.circle(x, y, {
                radius: 0.6,
                fill: colors.dark,
                stroke: colors.outline,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            this.rect(x - 0.4, y - 0.3, 0.8, 0.6, {
                fill: colors.gray,
                opacity: opts.opacity
            });
            this.rect(x - 0.2, y - 0.9, 0.4, 0.5, {
                fill: colors.light,
                stroke: colors.dark,
                strokeWidth: 0.07,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_ROAD:
            this.circle(x, y, {
                radius: 0.175,
                fill: colors.road,
                stroke: false,
                opacity: opts.opacity
            });
            if (!this.roads)
                this.roads = [];
            this.roads.push([x, y]);
            break;
        case STRUCTURE_RAMPART:
            this.circle(x, y, {
                radius: 0.65,
                fill: '#434C43',
                stroke: '#5D735F',
                strokeWidth: 0.10,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_WALL:
            this.circle(x, y, {
                radius: 0.40,
                fill: colors.dark,
                stroke: colors.light,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_STORAGE:
            let storageOutline = relPoly(x, y, [
                [-0.45, -0.55],
                [0, -0.65],
                [0.45, -0.55],
                [0.55, 0],
                [0.45, 0.55],
                [0, 0.65],
                [-0.45, 0.55],
                [-0.55, 0],
                [-0.45, -0.55],
            ]);
            this.poly(storageOutline, {
                stroke: colors.outline,
                strokeWidth: 0.05,
                fill: colors.dark,
                opacity: opts.opacity
            });
            this.rect(x - 0.35, y - 0.45, 0.7, 0.9, {
                fill: colors.energy,
                opacity: opts.opacity,
            });
            break;
        case STRUCTURE_OBSERVER:
            this.circle(x, y, {
                fill: colors.dark,
                radius: 0.45,
                stroke: colors.outline,
                strokeWidth: 0.05,
                opacity: opts.opacity
            });
            this.circle(x + 0.225, y, {
                fill: colors.outline,
                radius: 0.20,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_NUKER:
            let outline = [
                [0, -1],
                [-0.47, 0.2],
                [-0.5, 0.5],
                [0.5, 0.5],
                [0.47, 0.2],
                [0, -1],
            ];
            outline = relPoly(x, y, outline);
            this.poly(outline, {
                stroke: colors.outline,
                strokeWidth: 0.05,
                fill: colors.dark,
                opacity: opts.opacity
            });
            let inline = [
                [0, -.80],
                [-0.40, 0.2],
                [0.40, 0.2],
                [0, -.80],
            ];
            inline = relPoly(x, y, inline);
            this.poly(inline, {
                stroke: colors.outline,
                strokeWidth: 0.01,
                fill: colors.gray,
                opacity: opts.opacity
            });
            break;
        case STRUCTURE_CONTAINER:
            this.rect(x - 0.225, y - 0.3, 0.45, 0.6, {
                fill: 'yellow',
                opacity: opts.opacity,
                stroke: colors.dark,
                strokeWidth: 0.10,
            });
            break;
        default:
            this.circle(x, y, {
                fill: colors.light,
                radius: 0.35,
                stroke: colors.dark,
                strokeWidth: 0.20,
                opacity: opts.opacity
            });
            break;
    }
    return this;
};
const dirs = [
    [],
    [0, -1],
    [1, -1],
    [1, 0],
    [1, 1],
    [0, 1],
    [-1, 1],
    [-1, 0],
    [-1, -1]
];
RoomVisual.prototype.connectRoads = function (opts = {}) {
    _.defaults(opts, { opacity: 0.5 });
    let color = opts.color || colors.road || 'white';
    if (!this.roads)
        return;
    // this.text(this.roads.map(r=>r.join(',')).join(' '),25,23)
    this.roads.forEach((r) => {
        // this.text(`${r[0]},${r[1]}`,r[0],r[1],{ size: 0.2 })
        for (let i = 1; i <= 4; i++) {
            let d = dirs[i];
            let c = [r[0] + d[0], r[1] + d[1]];
            let rd = _.some(this.roads, r => r[0] == c[0] && r[1] == c[1]);
            // this.text(`${c[0]},${c[1]}`,c[0],c[1],{ size: 0.2, color: rd?'green':'red' })
            if (rd) {
                this.line(r[0], r[1], c[0], c[1], {
                    color: color,
                    width: 0.35,
                    opacity: opts.opacity
                });
            }
        }
    });
    return this;
};
RoomVisual.prototype.speech = function (text, x, y, opts = {}) {
    var background = !!opts.background ? opts.background : colors.speechBackground;
    var textcolor = !!opts.textcolor ? opts.textcolor : colors.speechText;
    // noinspection PointlessBooleanExpressionJS
    var textstyle = !!opts.textstyle ? opts.textstyle : false;
    var textsize = !!opts.textsize ? opts.textsize : speechSize;
    var textfont = !!opts.textfont ? opts.textfont : speechFont;
    var opacity = !!opts.opacity ? opts.opacity : 1;
    var fontstring = '';
    if (textstyle) {
        fontstring = textstyle + ' ';
    }
    fontstring += textsize + ' ' + textfont;
    let pointer = [
        [-0.2, -0.8],
        [0.2, -0.8],
        [0, -0.3]
    ];
    pointer = relPoly(x, y, pointer);
    pointer.push(pointer[0]);
    this.poly(pointer, {
        fill: background,
        stroke: background,
        opacity: opacity,
        strokeWidth: 0.0
    });
    this.text(text, x, y - 1, {
        color: textcolor,
        backgroundColor: background,
        backgroundPadding: 0.1,
        opacity: opacity,
        font: fontstring
    });
    return this;
};
RoomVisual.prototype.animatedPosition = function (x, y, opts = {}) {
    let color = !!opts.color ? opts.color : 'blue';
    let opacity = !!opts.opacity ? opts.opacity : 0.5;
    let radius = !!opts.radius ? opts.radius : 0.75;
    let frames = !!opts.frames ? opts.frames : 6;
    let angle = (Game.time % frames * 90 / frames) * (Math.PI / 180);
    let s = Math.sin(angle);
    let c = Math.cos(angle);
    let sizeMod = Math.abs(Game.time % frames - frames / 2) / 10;
    radius += radius * sizeMod;
    let points = [
        rotate(0, -radius, s, c, x, y),
        rotate(radius, 0, s, c, x, y),
        rotate(0, radius, s, c, x, y),
        rotate(-radius, 0, s, c, x, y),
        rotate(0, -radius, s, c, x, y),
    ];
    this.poly(points, { stroke: color, opacity: opacity });
    return this;
};
function rotate(x, y, s, c, px, py) {
    let xDelta = x * c - y * s;
    let yDelta = x * s + y * c;
    return { x: px + xDelta, y: py + yDelta };
}
function relPoly(x, y, poly) {
    return poly.map(p => {
        p[0] += x;
        p[1] += y;
        return p;
    });
}
RoomVisual.prototype.test = function () {
    let demopos = [19, 24];
    this.clear();
    this.structure(demopos[0] + 0, demopos[1] + 0, STRUCTURE_LAB);
    this.structure(demopos[0] + 1, demopos[1] + 1, STRUCTURE_TOWER);
    this.structure(demopos[0] + 2, demopos[1] + 0, STRUCTURE_LINK);
    this.structure(demopos[0] + 3, demopos[1] + 1, STRUCTURE_TERMINAL);
    this.structure(demopos[0] + 4, demopos[1] + 0, STRUCTURE_EXTENSION);
    this.structure(demopos[0] + 5, demopos[1] + 1, STRUCTURE_SPAWN);
    this.animatedPosition(demopos[0] + 7, demopos[1]);
    this.speech('This is a test!', demopos[0] + 10, demopos[1], { opacity: 0.7 });
    // this.infoBox(['This is', 'a test', 'mmmmmmmmmmmmm'], demopos[0] + 15, demopos[1]);
    return this;
};
const ColorSets = {
    white: ['#ffffff', '#4c4c4c'],
    grey: ['#b4b4b4', '#4c4c4c'],
    red: ['#ff7b7b', '#592121'],
    yellow: ['#fdd388', '#5d4c2e'],
    green: ['#00f4a2', '#236144'],
    blue: ['#50d7f9', '#006181'],
    purple: ['#a071ff', '#371383'],
};
const ResourceColors = {
    [RESOURCE_ENERGY]: ColorSets.yellow,
    [RESOURCE_POWER]: ColorSets.red,
    [RESOURCE_HYDROGEN]: ColorSets.grey,
    [RESOURCE_OXYGEN]: ColorSets.grey,
    [RESOURCE_UTRIUM]: ColorSets.blue,
    [RESOURCE_LEMERGIUM]: ColorSets.green,
    [RESOURCE_KEANIUM]: ColorSets.purple,
    [RESOURCE_ZYNTHIUM]: ColorSets.yellow,
    [RESOURCE_CATALYST]: ColorSets.red,
    [RESOURCE_GHODIUM]: ColorSets.white,
    [RESOURCE_HYDROXIDE]: ColorSets.grey,
    [RESOURCE_ZYNTHIUM_KEANITE]: ColorSets.grey,
    [RESOURCE_UTRIUM_LEMERGITE]: ColorSets.grey,
    [RESOURCE_UTRIUM_HYDRIDE]: ColorSets.blue,
    [RESOURCE_UTRIUM_OXIDE]: ColorSets.blue,
    [RESOURCE_KEANIUM_HYDRIDE]: ColorSets.purple,
    [RESOURCE_KEANIUM_OXIDE]: ColorSets.purple,
    [RESOURCE_LEMERGIUM_HYDRIDE]: ColorSets.green,
    [RESOURCE_LEMERGIUM_OXIDE]: ColorSets.green,
    [RESOURCE_ZYNTHIUM_HYDRIDE]: ColorSets.yellow,
    [RESOURCE_ZYNTHIUM_OXIDE]: ColorSets.yellow,
    [RESOURCE_GHODIUM_HYDRIDE]: ColorSets.white,
    [RESOURCE_GHODIUM_OXIDE]: ColorSets.white,
    [RESOURCE_UTRIUM_ACID]: ColorSets.blue,
    [RESOURCE_UTRIUM_ALKALIDE]: ColorSets.blue,
    [RESOURCE_KEANIUM_ACID]: ColorSets.purple,
    [RESOURCE_KEANIUM_ALKALIDE]: ColorSets.purple,
    [RESOURCE_LEMERGIUM_ACID]: ColorSets.green,
    [RESOURCE_LEMERGIUM_ALKALIDE]: ColorSets.green,
    [RESOURCE_ZYNTHIUM_ACID]: ColorSets.yellow,
    [RESOURCE_ZYNTHIUM_ALKALIDE]: ColorSets.yellow,
    [RESOURCE_GHODIUM_ACID]: ColorSets.white,
    [RESOURCE_GHODIUM_ALKALIDE]: ColorSets.white,
    [RESOURCE_CATALYZED_UTRIUM_ACID]: ColorSets.blue,
    [RESOURCE_CATALYZED_UTRIUM_ALKALIDE]: ColorSets.blue,
    [RESOURCE_CATALYZED_KEANIUM_ACID]: ColorSets.purple,
    [RESOURCE_CATALYZED_KEANIUM_ALKALIDE]: ColorSets.purple,
    [RESOURCE_CATALYZED_LEMERGIUM_ACID]: ColorSets.green,
    [RESOURCE_CATALYZED_LEMERGIUM_ALKALIDE]: ColorSets.green,
    [RESOURCE_CATALYZED_ZYNTHIUM_ACID]: ColorSets.yellow,
    [RESOURCE_CATALYZED_ZYNTHIUM_ALKALIDE]: ColorSets.yellow,
    [RESOURCE_CATALYZED_GHODIUM_ACID]: ColorSets.white,
    [RESOURCE_CATALYZED_GHODIUM_ALKALIDE]: ColorSets.white,
};
RoomVisual.prototype.resource = function (type, x, y, size = 0.25, opacity = 1) {
    if (type == RESOURCE_ENERGY || type == RESOURCE_POWER)
        this._fluid(type, x, y, size, opacity);
    else if ([RESOURCE_CATALYST, RESOURCE_HYDROGEN, RESOURCE_OXYGEN, RESOURCE_LEMERGIUM, RESOURCE_UTRIUM,
        RESOURCE_ZYNTHIUM, RESOURCE_KEANIUM]
        .includes(type))
        this._mineral(type, x, y, size, opacity);
    else if (ResourceColors[type] != undefined)
        this._compound(type, x, y, size, opacity);
    else
        return ERR_INVALID_ARGS;
    return OK;
};
RoomVisual.prototype._fluid = function (type, x, y, size = 0.25, opacity = 1) {
    this.circle(x, y, {
        radius: size,
        fill: ResourceColors[type][0],
        opacity: opacity,
    });
    this.text(type[0], x, y - (size * 0.1), {
        font: (size * 1.5),
        color: ResourceColors[type][1],
        backgroundColor: ResourceColors[type][0],
        backgroundPadding: 0,
        opacity: opacity
    });
};
RoomVisual.prototype._mineral = function (type, x, y, size = 0.25, opacity = 1) {
    this.circle(x, y, {
        radius: size,
        fill: ResourceColors[type][0],
        opacity: opacity,
    });
    this.circle(x, y, {
        radius: size * 0.8,
        fill: ResourceColors[type][1],
        opacity: opacity,
    });
    this.text(type, x, y + (size * 0.03), {
        font: 'bold ' + (size * 1.25) + ' arial',
        color: ResourceColors[type][0],
        backgroundColor: ResourceColors[type][1],
        backgroundPadding: 0,
        opacity: opacity
    });
};
RoomVisual.prototype._compound = function (type, x, y, size = 0.25, opacity = 1) {
    let label = type.replace('2', '₂');
    this.text(label, x, y, {
        font: 'bold ' + (size * 1) + ' arial',
        color: ResourceColors[type][1],
        backgroundColor: ResourceColors[type][0],
        backgroundPadding: 0.3 * size,
        opacity: opacity
    });
};

// Room prototypes - commonly used room properties and methods
// Logging =============================================================================================================
Object.defineProperty(Room.prototype, 'print', {
    get() {
        return '<a href="#!/room/' + Game.shard.name + '/' + this.name + '">' + this.name + '</a>';
    },
    configurable: true,
});
// Room properties =====================================================================================================
Object.defineProperty(Room.prototype, 'my', {
    get() {
        return this.controller && this.controller.my;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'isOutpost', {
    get() {
        return Overmind.colonyMap[this.name] != undefined;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'owner', {
    get() {
        return this.controller && this.controller.owner ? this.controller.owner.username : undefined;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'reservedByMe', {
    get() {
        return this.controller && this.controller.reservation && this.controller.reservation.username == MY_USERNAME;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'signedByMe', {
    get() {
        return this.controller && this.controller.sign && this.controller.sign.text == Memory.settings.signature;
    },
    configurable: true,
});
// Room properties: creeps =============================================================================================
// Creeps physically in the room
Object.defineProperty(Room.prototype, 'creeps', {
    get() {
        if (!this._creeps) {
            this._creeps = this.find(FIND_MY_CREEPS);
        }
        return this._creeps;
    },
    configurable: true,
});
// Room properties: hostiles ===========================================================================================
Object.defineProperty(Room.prototype, 'hostiles', {
    get() {
        if (!this._hostiles) {
            this._hostiles = this.find(FIND_HOSTILE_CREEPS);
        }
        return this._hostiles;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'invaders', {
    get() {
        if (!this._invaders) {
            this._invaders = _.filter(this.hostiles, (creep) => creep.owner.username == 'Invader');
        }
        return this._invaders;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'sourceKeepers', {
    get() {
        if (!this._sourceKeepers) {
            this._sourceKeepers = _.filter(this.hostiles, (creep) => creep.owner.username == 'Source Keeper');
        }
        return this._sourceKeepers;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'playerHostiles', {
    get() {
        if (!this._playerHostiles) {
            this._playerHostiles = _.filter(this.hostiles, (creep) => creep.owner.username != 'Invader'
                && creep.owner.username != 'Source Keeper');
        }
        return this._playerHostiles;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'dangerousHostiles', {
    get() {
        if (!this._dangerousHostiles) {
            if (this.my) {
                this._dangerousHostiles = _.filter(this.hostiles, (creep) => creep.getActiveBodyparts(ATTACK) > 0
                    || creep.getActiveBodyparts(WORK) > 0
                    || creep.getActiveBodyparts(RANGED_ATTACK) > 0
                    || creep.getActiveBodyparts(HEAL) > 0);
            }
            else {
                this._dangerousHostiles = _.filter(this.hostiles, (creep) => creep.getActiveBodyparts(ATTACK) > 0
                    || creep.getActiveBodyparts(RANGED_ATTACK) > 0
                    || creep.getActiveBodyparts(HEAL) > 0);
            }
        }
        return this._dangerousHostiles;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'dangerousPlayerHostiles', {
    get() {
        if (!this._dangerousPlayerHostiles) { // †
            this._dangerousPlayerHostiles = _.filter(this.playerHostiles, (c) => c.getActiveBodyparts(ATTACK) > 0
                || c.getActiveBodyparts(WORK) > 6
                || c.getActiveBodyparts(RANGED_ATTACK) > 0
                || c.getActiveBodyparts(HEAL) > 0);
        }
        return this._dangerousPlayerHostiles;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'fleeDefaults', {
    get() {
        if (!this._fleeDefaults) {
            this._fleeDefaults = []
                .concat(_.filter(this.hostiles, (c) => c.getActiveBodyparts(ATTACK) > 0
                || c.getActiveBodyparts(RANGED_ATTACK) > 0))
                .concat(_.filter(this.keeperLairs, (l) => (l.ticksToSpawn || Infinity) <= 10));
        }
        return this._fleeDefaults;
    },
    configurable: true,
});
// Hostile structures currently in the room
Object.defineProperty(Room.prototype, 'structures', {
    get() {
        if (!this._allStructures) {
            this._allStructures = this.find(FIND_STRUCTURES);
        }
        return this._allStructures;
    },
    configurable: true,
});
// Hostile structures currently in the room
Object.defineProperty(Room.prototype, 'hostileStructures', {
    get() {
        if (!this._hostileStructures) {
            this._hostileStructures = this.find(FIND_HOSTILE_STRUCTURES, { filter: (s) => s.hitsMax });
        }
        return this._hostileStructures;
    },
    configurable: true,
});
// Room properties: flags ==============================================================================================
// Flags physically in this room
Object.defineProperty(Room.prototype, 'flags', {
    get() {
        if (!this._flags) {
            this._flags = this.find(FIND_FLAGS);
        }
        return this._flags;
    },
    configurable: true,
});
// Room properties: structures =========================================================================================
Object.defineProperty(Room.prototype, 'constructionSites', {
    get() {
        if (!this._constructionSites) {
            this._constructionSites = this.find(FIND_MY_CONSTRUCTION_SITES);
        }
        return this._constructionSites;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'tombstones', {
    get() {
        if (!this._tombstones) {
            this._tombstones = this.find(FIND_TOMBSTONES);
        }
        return this._tombstones;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'drops', {
    get() {
        if (!this._drops) {
            this._drops = _.groupBy(this.find(FIND_DROPPED_RESOURCES), (r) => r.resourceType);
        }
        return this._drops;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'droppedEnergy', {
    get() {
        return this.drops[RESOURCE_ENERGY] || [];
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'droppedPower', {
    get() {
        return this.drops[RESOURCE_POWER] || [];
    },
    configurable: true,
});
// Object.defineProperties(Room.prototype, {
// // Spawns in the room
// spawns: {
// 	get() {
// 		return this.structures[STRUCTURE_SPAWN] || [];
// 	},
// },
//
// // All extensions in room
// extensions: {
// 	get() {
// 		return this.structures[STRUCTURE_EXTENSION] || [];
// 	},
// },
//
// // The extractor in the room, if present
// extractor: {
// 	get() {
// 		return (this.structures[STRUCTURE_EXTRACTOR] || [])[0] || undefined;
// 	},
// },
//
// // All containers in the room
// containers: {
// 	get() {
// 		return this.structures[STRUCTURE_CONTAINER] || [];
// 	},
// },
//
// // All container-like objects in the room
// storageUnits: {
// 	get() {
// 		if (!this.structures['storageUnits']) {
// 			let storageUnits = [].concat(this.structures[STRUCTURE_CONTAINER],
// 										 this.structures[STRUCTURE_STORAGE],
// 										 this.structures[STRUCTURE_TERMINAL]);
// 			this.structures['storageUnits'] = _.compact(_.flatten(storageUnits));
// 		}
// 		return this.structures['storageUnits'] || [];
// 	},
// },
//
// // Towers
// towers: {
// 	get() {
// 		return this.structures[STRUCTURE_TOWER] || [];
// 	},
// },
//
// // Links, some of which are assigned to virtual components
// links: {
// 	get() {
// 		return this.structures[STRUCTURE_LINK] || [];
// 	},
// },
//
// // Labs
// labs: {
// 	get() {
// 		return this.structures[STRUCTURE_LAB] || [];
// 	},
// },
//
// // All energy sources
// sources: {
// 	get() {
// 		return this.find(FIND_SOURCES) || [];
// 	},
// },
//
// mineral: {
// 	get() {
// 		return this.find(FIND_MINERALS)[0];
// 	},
// },
//
// keeperLairs: {
// 	get() {
// 		return this.structures[STRUCTURE_KEEPER_LAIR] || [];
// 	},
// },
//
// // All non-barrier, non-road repairable objects
// repairables: {
// 	get() {
// 		if (!this.structures['repairables']) {
// 			let repairables: Structure[] = [];
// 			for (let structureType in this.structures) {
// 				if (structureType != STRUCTURE_WALL &&
// 					structureType != STRUCTURE_RAMPART &&
// 					structureType != STRUCTURE_ROAD) {
// 					repairables = repairables.concat(this.structures[structureType]);
// 				}
// 			}
// 			this.structures['repairables'] = _.compact(_.flatten(repairables));
// 		}
// 		return this.structures['repairables'] || [];
// 	},
// },
//
// // All containers in the room
// roads: {
// 	get() {
// 		return this.structures[STRUCTURE_ROAD] || [];
// 	},
// },
//
// // All construction sites
// constructionSites: {
// 	get() {
// 		return Overmind.cache.constructionSites[this.name] || [];
// 	},
// },
//
// // // All non-road construction sites
// // structureSites: {
// // 	get() {
// // 		return Overmind.cache.structureSites[this.name] || [];
// // 	},
// // },
// //
// // // All construction sites for roads
// // roadSites: {
// // 	get() {
// // 		return Overmind.cache.roadSites[this.name] || [];
// // 	},
// // },
//
// // All walls and ramparts
// barriers: {
// 	get() {
// 		if (!this.structures['barriers']) {
// 			let barriers = [].concat(this.structures[STRUCTURE_WALL],
// 									 this.structures[STRUCTURE_RAMPART]);
// 			this.structures['barriers'] = _.compact(_.flatten(barriers));
// 		}
// 		return this.structures['barriers'] || [];
// 	},
// },
//
// ramparts: {
// 	get() {
// 		return this.structures[STRUCTURE_RAMPART] || [];
// 	},
// },
//
// walls: {
// 	get() {
// 		return this.structures[STRUCTURE_WALL] || [];
// 	},
// },
// });

// Intra- and inter-tick structure caching, adapted from semperRabbit's IVM module †
var roomStructureIDs = {};
var roomStructuresExpiration = {};
const multipleList = [
    STRUCTURE_SPAWN, STRUCTURE_EXTENSION, STRUCTURE_ROAD, STRUCTURE_WALL,
    STRUCTURE_RAMPART, STRUCTURE_KEEPER_LAIR, STRUCTURE_PORTAL, STRUCTURE_LINK,
    STRUCTURE_TOWER, STRUCTURE_LAB, STRUCTURE_CONTAINER, STRUCTURE_POWER_BANK,
];
const singleList = [
    STRUCTURE_OBSERVER, STRUCTURE_POWER_SPAWN, STRUCTURE_EXTRACTOR, STRUCTURE_NUKER,
];
const notRepairable = [STRUCTURE_KEEPER_LAIR, STRUCTURE_PORTAL, STRUCTURE_POWER_BANK];
const STRUCTURE_TIMEOUT = onPublicServer() ? 50 : 10;
Room.prototype._refreshStructureCache = function () {
    // if cache is expired or doesn't exist
    if (!roomStructuresExpiration[this.name]
        || !roomStructureIDs[this.name]
        || Game.time > roomStructuresExpiration[this.name]) {
        roomStructuresExpiration[this.name] = getCacheExpiration(STRUCTURE_TIMEOUT);
        roomStructureIDs[this.name] = _.mapValues(_.groupBy(this.find(FIND_STRUCTURES), (s) => s.structureType), (structures) => _.map(structures, s => s.id));
    }
};
multipleList.forEach(function (type) {
    Object.defineProperty(Room.prototype, type + 's', {
        get: function () {
            if (this['_' + type + 's']) {
                return this['_' + type + 's'];
            }
            else {
                this._refreshStructureCache();
                if (roomStructureIDs[this.name][type]) {
                    return this['_' + type + 's'] = _.compact(_.map(roomStructureIDs[this.name][type], Game.getObjectById));
                }
                else {
                    return this['_' + type + 's'] = [];
                }
            }
        },
        configurable: true,
    });
});
singleList.forEach(function (type) {
    Object.defineProperty(Room.prototype, type, {
        get: function () {
            if (this['_' + type]) {
                return this['_' + type];
            }
            else {
                this._refreshStructureCache();
                if (roomStructureIDs[this.name][type]) {
                    return this['_' + type] = Game.getObjectById(roomStructureIDs[this.name][type][0]);
                }
                else {
                    return this['_' + type] = undefined;
                }
            }
        },
        configurable: true,
    });
});
Object.defineProperty(Room.prototype, 'storageUnits', {
    get() {
        if (!this._storageUnits) {
            this._storageUnits = _.compact([this.storage, this.terminal]).concat(this.containers);
        }
        return this._storageUnits;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'sources', {
    get() {
        if (!this._sources) {
            this._sources = this.find(FIND_SOURCES);
        }
        return this.find(FIND_SOURCES);
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'mineral', {
    get() {
        if (!this._mineral) {
            this._mineral = this.find(FIND_MINERALS)[0];
        }
        return this._mineral;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'repairables', {
    get() {
        if (!this._repairables) {
            this._refreshStructureCache();
            if (roomStructureIDs[this.name]['repairables']) {
                return this._repairables = _.compact(_.map(roomStructureIDs[this.name]['repairables'], Game.getObjectById));
            }
            else {
                let repairables = [];
                for (let structureType of singleList) {
                    if (this[structureType]) {
                        repairables.push(this[structureType]);
                    }
                }
                for (let structureType of multipleList) {
                    if (structureType != STRUCTURE_WALL &&
                        structureType != STRUCTURE_RAMPART &&
                        structureType != STRUCTURE_ROAD &&
                        !notRepairable.includes(structureType)) {
                        repairables = repairables.concat(this[structureType + 's']);
                    }
                }
                roomStructureIDs[this.name]['repairables'] = _.map(repairables, s => s.id);
                return this._repairables = repairables;
            }
        }
        return this._repairables;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'walkableRamparts', {
    get() {
        if (!this._walkableRamparts) {
            this._refreshStructureCache();
            if (roomStructureIDs[this.name]['walkableRamparts']) {
                return this._walkableRamparts = _.compact(_.map(roomStructureIDs[this.name]['walkableRamparts'], Game.getObjectById));
            }
            else {
                let walkableRamparts = _.filter(this.ramparts, (r) => r.pos.isWalkable(true));
                roomStructureIDs[this.name]['walkableRamparts'] = _.map(walkableRamparts, r => r.id);
                return this._walkableRamparts = walkableRamparts;
            }
        }
        return this._walkableRamparts;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'rechargeables', {
    get() {
        if (!this._rechargeables) {
            this._rechargeables = [...this.storageUnits,
                ...this.droppedEnergy,
                ...this.tombstones];
        }
        return this._rechargeables;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'barriers', {
    get() {
        if (!this._barriers) {
            this._barriers = [].concat(this.ramparts, this.constructedWalls);
        }
        return this._barriers;
    },
    configurable: true,
});
Object.defineProperty(Room.prototype, 'walls', {
    get() {
        return this.constructedWalls;
    },
    configurable: true,
});

// All structure prototypes
Object.defineProperty(Structure.prototype, 'isWalkable', {
    get() {
        return this.structureType == STRUCTURE_ROAD ||
            this.structureType == STRUCTURE_CONTAINER ||
            (this.structureType == STRUCTURE_RAMPART && (this.my ||
                this.isPublic));
    },
    configurable: true,
});
// Container prototypes ================================================================================================
Object.defineProperty(StructureContainer.prototype, 'energy', {
    get() {
        return this.store[RESOURCE_ENERGY];
    },
    configurable: true,
});
Object.defineProperty(StructureContainer.prototype, 'isFull', {
    get() {
        return _.sum(this.store) >= this.storeCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureContainer.prototype, 'isEmpty', {
    get() {
        return _.sum(this.store) == 0;
    },
    configurable: true,
});
// Controller prototypes ===============================================================================================
Object.defineProperty(StructureController.prototype, 'reservedByMe', {
    get: function () {
        return this.reservation && this.reservation.username == MY_USERNAME;
    },
    configurable: true,
});
Object.defineProperty(StructureController.prototype, 'signedByMe', {
    get: function () {
        return this.sign && this.sign.text == Memory.settings.signature && Game.time - this.sign.time < 250000;
    },
    configurable: true,
});
Object.defineProperty(StructureController.prototype, 'signedByScreeps', {
    get: function () {
        return this.sign && this.sign.username == 'Screeps';
    },
    configurable: true,
});
StructureController.prototype.needsReserving = function (reserveBuffer) {
    return !this.reservation || (this.reservedByMe && this.reservation.ticksToEnd < reserveBuffer);
};
// Extension prototypes ================================================================================================
Object.defineProperty(StructureExtension.prototype, 'isFull', {
    get() {
        return this.energy >= this.energyCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureExtension.prototype, 'isEmpty', {
    get() {
        return this.energy == 0;
    },
    configurable: true,
});
// Link prototypes =====================================================================================================
Object.defineProperty(StructureLink.prototype, 'isFull', {
    get() {
        return this.energy >= this.energyCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureLink.prototype, 'isEmpty', {
    get() {
        return this.energy == 0;
    },
    configurable: true,
});
// Nuker prototypes ====================================================================================================
// PowerSpawn prototypes ===============================================================================================
// Spawn prototypes ====================================================================================================
Object.defineProperty(StructureSpawn.prototype, 'isFull', {
    get() {
        return this.energy >= this.energyCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureSpawn.prototype, 'isEmpty', {
    get() {
        return this.energy == 0;
    },
    configurable: true,
});
// Storage prototypes ==================================================================================================
Object.defineProperty(StructureStorage.prototype, 'energy', {
    get() {
        return this.store[RESOURCE_ENERGY];
    },
    configurable: true,
});
Object.defineProperty(StructureStorage.prototype, 'isFull', {
    get() {
        return _.sum(this.store) >= this.storeCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureStorage.prototype, 'isEmpty', {
    get() {
        return _.sum(this.store) == 0;
    },
    configurable: true,
});
// Terminal prototypes =================================================================================================
Object.defineProperty(StructureTerminal.prototype, 'energy', {
    get() {
        return this.store[RESOURCE_ENERGY];
    },
    configurable: true,
});
Object.defineProperty(StructureTerminal.prototype, 'isFull', {
    get() {
        return _.sum(this.store) >= this.storeCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureTerminal.prototype, 'isEmpty', {
    get() {
        return _.sum(this.store) == 0;
    },
    configurable: true,
});
// StructureTerminal.prototype._send = StructureTerminal.prototype.send;
// StructureTerminal.prototype.send = function(resourceType: ResourceConstant, amount: number, destination: string,
// 											description?: string): ScreepsReturnCode {
// 	// Log stats
// 	let origin = this.room.name;
// 	let response = this._send(resourceType, amount, destination, description);
// 	if (response == OK) {
// 		TerminalNetwork.logTransfer(resourceType,amount,origin, destination)
// 	}
// 	return response;
// };
// Tower prototypes
Object.defineProperty(StructureTower.prototype, 'isFull', {
    get() {
        return this.energy >= this.energyCapacity;
    },
    configurable: true,
});
Object.defineProperty(StructureTower.prototype, 'isEmpty', {
    get() {
        return this.energy == 0;
    },
    configurable: true,
});
// Tombstone prototypes ================================================================================================
Object.defineProperty(Tombstone.prototype, 'energy', {
    get() {
        return this.store[RESOURCE_ENERGY];
    },
    configurable: true,
});

"use strict";
String.prototype.padRight = function (length, char = ' ') {
    return this + char.repeat(Math.max(length - this.length, 0));
};
String.prototype.padLeft = function (length, char = ' ') {
    return char.repeat(Math.max(length - this.length, 0)) + this;
};
Number.prototype.toPercent = function (decimals = 0) {
    return (this * 100).toFixed(decimals) + '%';
};
Number.prototype.truncate = function (decimals) {
    var re = new RegExp('(\\d+\\.\\d{' + decimals + '})(\\d)'), m = this.toString().match(re);
    return m ? parseFloat(m[1]) : this.valueOf();
};
Object.defineProperty(ConstructionSite.prototype, 'isWalkable', {
    get() {
        return this.structureType == STRUCTURE_ROAD ||
            this.structureType == STRUCTURE_CONTAINER ||
            this.structureType == STRUCTURE_RAMPART;
    },
    configurable: true,
});

var Log_1;
var LogLevels;
(function (LogLevels) {
    LogLevels[LogLevels["ERROR"] = 0] = "ERROR";
    LogLevels[LogLevels["WARNING"] = 1] = "WARNING";
    LogLevels[LogLevels["ALERT"] = 2] = "ALERT";
    LogLevels[LogLevels["INFO"] = 3] = "INFO";
    LogLevels[LogLevels["DEBUG"] = 4] = "DEBUG"; // log.level = 4
})(LogLevels || (LogLevels = {}));
/**
 * Debug level for log output
 */
const LOG_LEVEL = LogLevels.INFO;
/**
 * Prepend log output with current tick number.
 */
const LOG_PRINT_TICK = true;
/**
 * Prepend log output with source line.
 */
const LOG_PRINT_LINES = false;
/**
 * Load source maps and resolve source lines back to typeascript.
 */
const LOG_LOAD_SOURCE_MAP = false;
/**
 * Maximum padding for source links (for aligning log output).
 */
const LOG_MAX_PAD = 100;
/**
 * VSC location, used to create links back to source.
 * Repo and revision are filled in at build time for git repositories.
 */
const LOG_VSC = { repo: '@@_repo_@@', revision: '@@_revision_@@', valid: false };
// export const LOG_VSC = { repo: "@@_repo_@@", revision: __REVISION__, valid: false };
/**
 * URL template for VSC links, this one works for github and gitlab.
 */
const LOG_VSC_URL_TEMPLATE = (path, line) => {
    return `${LOG_VSC.repo}/blob/${LOG_VSC.revision}/${path}#${line}`;
};
// <caller> (<source>:<line>:<column>)
const stackLineRe = /([^ ]*) \(([^:]*):([0-9]*):([0-9]*)\)/;
const FATAL = -1;
const fatalColor = '#d65156';
function resolve(fileLine) {
    const split = _.trim(fileLine).match(stackLineRe);
    if (!split || !Log.sourceMap) {
        return { compiled: fileLine, final: fileLine };
    }
    const pos = { column: parseInt(split[4], 10), line: parseInt(split[3], 10) };
    const original = Log.sourceMap.originalPositionFor(pos);
    const line = `${split[1]} (${original.source}:${original.line})`;
    const out = {
        caller: split[1],
        compiled: fileLine,
        final: line,
        line: original.line,
        original: line,
        path: original.source,
    };
    return out;
}
function makeVSCLink(pos) {
    if (!LOG_VSC.valid || !pos.caller || !pos.path || !pos.line || !pos.original) {
        return pos.final;
    }
    return link(vscUrl(pos.path, `L${pos.line.toString()}`), pos.original);
}
function tooltip(str, tooltip) {
    return `<abbr title='${tooltip}'>${str}</abbr>`;
}
function vscUrl(path, line) {
    return LOG_VSC_URL_TEMPLATE(path, line);
}
function link(href, title) {
    return `<a href='${href}' target="_blank">${title}</a>`;
}
function time() {
    return color(Game.time.toString(), 'gray');
}
function debug(thing, ...args) {
    if (thing.memory && thing.memory.debug) {
        this.debug(`${thing.name} @ ${thing.pos.print}: `, args);
    }
}
let Log = Log_1 = class Log {
    constructor() {
        this._maxFileString = 0;
        _.defaultsDeep(Memory, {
            settings: {
                log: {
                    level: LOG_LEVEL,
                    showSource: LOG_PRINT_LINES,
                    showTick: LOG_PRINT_TICK,
                }
            }
        });
    }
    static loadSourceMap() {
        // try {
        // 	// tslint:disable-next-line
        // 	const map = require('main.js.map');
        // 	if (map) {
        // 		Log.sourceMap = new SourceMapConsumer(map);
        // 	}
        // } catch (err) {
        console.log('Source mapping deprecated.');
        // }
    }
    get level() {
        return Memory.settings.log.level;
    }
    setLogLevel(value) {
        let changeValue = true;
        switch (value) {
            case LogLevels.ERROR:
                console.log(`Logging level set to ${value}. Displaying: ERROR.`);
                break;
            case LogLevels.WARNING:
                console.log(`Logging level set to ${value}. Displaying: ERROR, WARNING.`);
                break;
            case LogLevels.ALERT:
                console.log(`Logging level set to ${value}. Displaying: ERROR, WARNING, ALERT.`);
                break;
            case LogLevels.INFO:
                console.log(`Logging level set to ${value}. Displaying: ERROR, WARNING, ALERT, INFO.`);
                break;
            case LogLevels.DEBUG:
                console.log(`Logging level set to ${value}. Displaying: ERROR, WARNING, ALERT, INFO, DEBUG.`);
                break;
            default:
                console.log(`Invalid input: ${value}. Loging level can be set to integers between `
                    + LogLevels.ERROR + ' and ' + LogLevels.DEBUG + ', inclusive.');
                changeValue = false;
                break;
        }
        if (changeValue) {
            Memory.settings.log.level = value;
        }
    }
    get showSource() {
        return Memory.settings.log.showSource;
    }
    set showSource(value) {
        Memory.settings.log.showSource = value;
    }
    get showTick() {
        return Memory.settings.log.showTick;
    }
    set showTick(value) {
        Memory.settings.log.showTick = value;
    }
    trace(error) {
        if (this.level >= LogLevels.ERROR && error.stack) {
            console.log(this.resolveStack(error.stack));
        }
        return this;
    }
    throw(e) {
        console.log.apply(this, this.buildArguments(FATAL).concat([color(e.toString(), fatalColor)]));
    }
    error(...args) {
        if (this.level >= LogLevels.ERROR) {
            console.log.apply(this, this.buildArguments(LogLevels.ERROR).concat([].slice.call(args)));
        }
        return undefined;
    }
    warning(...args) {
        if (this.level >= LogLevels.WARNING) {
            console.log.apply(this, this.buildArguments(LogLevels.WARNING).concat([].slice.call(args)));
        }
        return undefined;
    }
    alert(...args) {
        if (this.level >= LogLevels.ALERT) {
            console.log.apply(this, this.buildArguments(LogLevels.ALERT).concat([].slice.call(args)));
        }
        return undefined;
    }
    notify(message) {
        this.alert(message);
        Game.notify(message);
        return undefined;
    }
    info(...args) {
        if (this.level >= LogLevels.INFO) {
            console.log.apply(this, this.buildArguments(LogLevels.INFO).concat([].slice.call(args)));
        }
        return undefined;
    }
    debug(...args) {
        if (this.level >= LogLevels.DEBUG) {
            console.log.apply(this, this.buildArguments(LogLevels.DEBUG).concat([].slice.call(args)));
        }
    }
    debugCreep(creep, ...args) {
        if (creep.memory && creep.memory.debug) {
            this.debug(`${creep.name} @ ${creep.pos.print}: `, args);
        }
    }
    printObject(obj) {
        console.log.apply(this, this.buildArguments(LogLevels.DEBUG).concat(JSON.stringify(obj)));
    }
    getFileLine(upStack = 4) {
        const stack = new Error('').stack;
        if (stack) {
            const lines = stack.split('\n');
            if (lines.length > upStack) {
                const originalLines = _.drop(lines, upStack).map(resolve);
                const hoverText = _.map(originalLines, 'final').join('&#10;');
                return this.adjustFileLine(originalLines[0].final, tooltip(makeVSCLink(originalLines[0]), hoverText));
            }
        }
        return '';
    }
    buildArguments(level) {
        const out = [];
        switch (level) {
            case LogLevels.ERROR:
                out.push(color('ERROR  ', 'red'));
                break;
            case LogLevels.WARNING:
                out.push(color('WARNING', 'orange'));
                break;
            case LogLevels.ALERT:
                out.push(color('ALERT  ', 'yellow'));
                break;
            case LogLevels.INFO:
                out.push(color('INFO   ', 'green'));
                break;
            case LogLevels.DEBUG:
                out.push(color('DEBUG  ', 'gray'));
                break;
            case FATAL:
                out.push(color('FATAL  ', fatalColor));
                break;
            default:
                break;
        }
        if (this.showTick) {
            out.push(time());
        }
        if (this.showSource && level <= LogLevels.ERROR) {
            out.push(this.getFileLine());
        }
        return out;
    }
    resolveStack(stack) {
        if (!Log_1.sourceMap) {
            return stack;
        }
        return _.map(stack.split('\n').map(resolve), 'final').join('\n');
    }
    adjustFileLine(visibleText, line) {
        const newPad = Math.max(visibleText.length, this._maxFileString);
        this._maxFileString = Math.min(newPad, LOG_MAX_PAD);
        return `|${_.padRight(line, line.length + this._maxFileString - visibleText.length, ' ')}|`;
    }
};
Log = Log_1 = __decorate([
    profile
], Log);
if (LOG_LOAD_SOURCE_MAP) {
    Log.loadSourceMap();
}
const log = new Log();

/**
 * Creep tasks setup instructions
 *
 * Javascript:
 * 1. In main.js:    require("tasks/prototypes.js");
 * 2. As needed:    var Tasks = require("<path to Tasks.js>");
 *
 * Typescript:
 * 1. In main.ts:    import "./tasks/prototypes";
 * 2. As needed:    import {Tasks} from "<path to Tasks.ts>"
 *
 * If you use Travler, change all occurrences of creep.moveTo() to creep.goTo()
 */
/* An abstract class for encapsulating creep actions. This generalizes the concept of "do action X to thing Y until
 * condition Z is met" and saves a lot of convoluted and duplicated code in creep logic. A Task object contains
 * the necessary logic for traveling to a target, performing a task, and realizing when a task is no longer sensible
 * to continue.*/
let Task = class Task {
    constructor(taskName, target, options = {}) {
        // Parameters for the task
        this.name = taskName;
        this._creep = {
            name: '',
        };
        if (target) { // Handles edge cases like when you're done building something and target disappears
            this._target = {
                ref: target.ref,
                _pos: target.pos,
            };
        }
        else {
            this._target = {
                ref: '',
                _pos: {
                    x: -1,
                    y: -1,
                    roomName: '',
                }
            };
        }
        this._parent = null;
        this.settings = {
            targetRange: 1,
            workOffRoad: false,
            oneShot: false,
            timeout: Infinity,
            blind: true,
        };
        this.tick = Game.time;
        this.options = options;
        this.data = {};
    }
    get proto() {
        return {
            name: this.name,
            _creep: this._creep,
            _target: this._target,
            _parent: this._parent,
            tick: this.tick,
            options: this.options,
            data: this.data,
        };
    }
    set proto(protoTask) {
        // Don't write to this.name; used in task switcher
        this._creep = protoTask._creep;
        this._target = protoTask._target;
        this._parent = protoTask._parent;
        this.tick = protoTask.tick;
        this.options = protoTask.options;
        this.data = protoTask.data;
    }
    // Getter/setter for task.creep
    get creep() {
        // Returns zerg wrapper instead of creep to use monkey-patched functions
        return Overmind.zerg[this._creep.name];
    }
    set creep(creep) {
        this._creep.name = creep.name;
        if (this._parent) {
            this.parent.creep = creep;
        }
    }
    // Dereferences the target
    get target() {
        return deref(this._target.ref);
    }
    // Dereferences the saved target position; useful for situations where you might lose vision
    get targetPos() {
        // refresh if you have visibility of the target
        if (!this._targetPos) {
            if (this.target) {
                this._target._pos = this.target.pos;
            }
            this._targetPos = derefRoomPosition(this._target._pos);
        }
        return this._targetPos;
    }
    // Getter/setter for task parent
    get parent() {
        return (this._parent ? initializeTask(this._parent) : null);
    }
    set parent(parentTask) {
        this._parent = parentTask ? parentTask.proto : null;
        // If the task is already assigned to a creep, update their memory
        if (this.creep) {
            this.creep.task = this;
        }
    }
    // Return a list of [this, this.parent, this.parent.parent, ...] as tasks
    get manifest() {
        let manifest = [this];
        let parent = this.parent;
        while (parent) {
            manifest.push(parent);
            parent = parent.parent;
        }
        return manifest;
    }
    // Return a list of [this.target, this.parent.target, ...] without fully instantiating the list of tasks
    get targetManifest() {
        let targetRefs = [this._target.ref];
        let parent = this._parent;
        while (parent) {
            targetRefs.push(parent._target.ref);
            parent = parent._parent;
        }
        return _.map(targetRefs, ref => deref(ref));
    }
    // Return a list of [this.target, this.parent.target, ...] without fully instantiating the list of tasks
    get targetPosManifest() {
        let targetPositions = [this._target._pos];
        let parent = this._parent;
        while (parent) {
            targetPositions.push(parent._target._pos);
            parent = parent._parent;
        }
        return _.map(targetPositions, protoPos => derefRoomPosition(protoPos));
    }
    // Fork the task, assigning a new task to the creep with this task as its parent
    fork(newTask) {
        newTask.parent = this;
        if (this.creep) {
            this.creep.task = newTask;
        }
        return newTask;
    }
    isValid() {
        let validTask = false;
        if (this.creep) {
            validTask = this.isValidTask() && Game.time - this.tick < this.settings.timeout;
        }
        let validTarget = false;
        if (this.target) {
            validTarget = this.isValidTarget();
        }
        else if ((this.settings.blind || this.options.blind) && !Game.rooms[this.targetPos.roomName]) {
            // If you can't see the target's room but you have blind enabled, then that's okay
            validTarget = true;
        }
        // Return if the task is valid; if not, finalize/delete the task and return false
        if (validTask && validTarget) {
            return true;
        }
        else {
            // Switch to parent task if there is one
            this.finish();
            let isValid = this.parent ? this.parent.isValid() : false;
            return isValid;
        }
    }
    /* Move to within range of the target */
    moveToTarget(range = this.settings.targetRange) {
        return this.creep.goTo(this.targetPos, { range: range });
    }
    /* Moves to the next position on the agenda if specified - call this in some tasks after work() is completed */
    moveToNextPos() {
        if (this.options.nextPos) {
            let nextPos = derefRoomPosition(this.options.nextPos);
            return this.creep.goTo(nextPos);
        }
    }
    // Return expected number of ticks until creep arrives at its first destination
    get eta() {
        if (this.creep && this.creep.memory._go && this.creep.memory._go.path) {
            return this.creep.memory._go.path.length;
        }
    }
    // Execute this task each tick. Returns nothing unless work is done.
    run() {
        if (this.isWorking) {
            delete this.creep.memory._go;
            // if (this.settings.workOffRoad) { // this is disabled as movement priorities makes it unnecessary
            // 	// Move to somewhere nearby that isn't on a road
            // 	this.creep.park(this.targetPos, true);
            // }
            let result = this.work();
            if (this.settings.oneShot && result === OK) {
                this.finish();
            }
            return result;
        }
        else {
            this.moveToTarget();
        }
    }
    get isWorking() {
        return this.creep.pos.inRangeToPos(this.targetPos, this.settings.targetRange) && !this.creep.pos.isEdge;
    }
    // Finalize the task and switch to parent task (or null if there is none)
    finish() {
        this.moveToNextPos();
        if (this.creep) {
            this.creep.task = this.parent;
        }
        else {
            log.debug(`No creep executing ${this.name}! Proto: ${JSON.stringify(this.proto)}`);
        }
    }
};
Task = __decorate([
    profile
], Task);

const attackTaskName = 'attack';
let TaskAttack = class TaskAttack extends Task {
    constructor(target, options = {}) {
        super(attackTaskName, target, options);
        // Settings
        this.settings.targetRange = 3;
    }
    isValidTask() {
        return (this.creep.getActiveBodyparts(ATTACK) > 0 || this.creep.getActiveBodyparts(RANGED_ATTACK) > 0);
    }
    isValidTarget() {
        return this.target && this.target.hits > 0;
    }
    work() {
        let creep = this.creep;
        let target = this.target;
        let attackReturn = 0;
        let rangedAttackReturn = 0;
        if (creep.getActiveBodyparts(ATTACK) > 0) {
            if (creep.pos.isNearTo(target)) {
                attackReturn = creep.attack(target);
            }
            else {
                attackReturn = this.moveToTarget(1); // approach target if you also have attack parts
            }
        }
        if (creep.pos.inRangeTo(target, 3) && creep.getActiveBodyparts(RANGED_ATTACK) > 0) {
            rangedAttackReturn = creep.rangedAttack(target);
        }
        if (attackReturn == OK && rangedAttackReturn == OK) {
            return OK;
        }
        else {
            if (attackReturn != OK) {
                return rangedAttackReturn;
            }
            else {
                return attackReturn;
            }
        }
    }
};
TaskAttack = __decorate([
    profile
], TaskAttack);

const buildTaskName = 'build';
let TaskBuild = class TaskBuild extends Task {
    constructor(target, options = {}) {
        super(buildTaskName, target, options);
        // Settings
        this.settings.targetRange = 3;
        this.settings.workOffRoad = true;
    }
    isValidTask() {
        return this.creep.carry.energy > 0;
    }
    isValidTarget() {
        return this.target && this.target.my && this.target.progress < this.target.progressTotal;
    }
    work() {
        // Fixes issue #9 - workers freeze if creep sitting on square
        if (!this.target.isWalkable) {
            let creepOnTarget = this.target.pos.lookFor(LOOK_CREEPS)[0];
            if (creepOnTarget) {
                const zerg = Overmind.zerg[creepOnTarget.name];
                if (zerg) {
                    this.creep.say('move pls');
                    zerg.moveOffCurrentPos();
                }
            }
        }
        return this.creep.build(this.target);
    }
};
TaskBuild = __decorate([
    profile
], TaskBuild);

const claimTaskName = 'claim';
let TaskClaim = class TaskClaim extends Task {
    constructor(target, options = {}) {
        super(claimTaskName, target, options);
        // Settings
    }
    isValidTask() {
        return (this.creep.getActiveBodyparts(CLAIM) > 0);
    }
    isValidTarget() {
        return (this.target != null && (!this.target.room || !this.target.owner));
    }
    work() {
        const result = this.creep.claimController(this.target);
        if (result == OK) {
            Overmind.shouldBuild = true; // rebuild the overmind object on the next tick to account for new room
        }
        return result;
    }
};
TaskClaim = __decorate([
    profile
], TaskClaim);

const dismantleTaskName = 'dismantle';
let TaskDismantle = class TaskDismantle extends Task {
    constructor(target, options = {}) {
        super(dismantleTaskName, target, options);
        this.settings.timeout = 100;
    }
    isValidTask() {
        return (this.creep.getActiveBodyparts(WORK) > 0);
    }
    isValidTarget() {
        return this.target && this.target.hits > 0;
    }
    work() {
        return this.creep.dismantle(this.target);
    }
};
TaskDismantle = __decorate([
    profile
], TaskDismantle);

const fortifyTaskName = 'fortify';
let TaskFortify = class TaskFortify extends Task {
    constructor(target, options = {}) {
        super(fortifyTaskName, target, options);
        // Settings
        this.settings.timeout = 100; // Don't want workers to fortify indefinitely
        this.settings.targetRange = 3;
        this.settings.workOffRoad = true;
    }
    isValidTask() {
        return (this.creep.carry.energy > 0); // Times out once creep is out of energy
    }
    isValidTarget() {
        return this.target && this.target.hits < this.target.hitsMax;
    }
    work() {
        return this.creep.repair(this.target);
    }
};
TaskFortify = __decorate([
    profile
], TaskFortify);

const RESOURCE_IMPORTANCE = [
    RESOURCE_CATALYZED_GHODIUM_ALKALIDE,
    RESOURCE_CATALYZED_GHODIUM_ACID,
    RESOURCE_CATALYZED_ZYNTHIUM_ALKALIDE,
    RESOURCE_CATALYZED_ZYNTHIUM_ACID,
    RESOURCE_CATALYZED_LEMERGIUM_ALKALIDE,
    RESOURCE_CATALYZED_LEMERGIUM_ACID,
    RESOURCE_CATALYZED_KEANIUM_ALKALIDE,
    RESOURCE_CATALYZED_KEANIUM_ACID,
    RESOURCE_CATALYZED_UTRIUM_ALKALIDE,
    RESOURCE_CATALYZED_UTRIUM_ACID,
    RESOURCE_POWER,
    RESOURCE_GHODIUM_ALKALIDE,
    RESOURCE_GHODIUM_ACID,
    RESOURCE_ZYNTHIUM_ALKALIDE,
    RESOURCE_ZYNTHIUM_ACID,
    RESOURCE_LEMERGIUM_ALKALIDE,
    RESOURCE_LEMERGIUM_ACID,
    RESOURCE_KEANIUM_ALKALIDE,
    RESOURCE_KEANIUM_ACID,
    RESOURCE_UTRIUM_ALKALIDE,
    RESOURCE_UTRIUM_ACID,
    RESOURCE_GHODIUM_OXIDE,
    RESOURCE_GHODIUM_HYDRIDE,
    RESOURCE_ZYNTHIUM_OXIDE,
    RESOURCE_ZYNTHIUM_HYDRIDE,
    RESOURCE_LEMERGIUM_OXIDE,
    RESOURCE_LEMERGIUM_HYDRIDE,
    RESOURCE_KEANIUM_OXIDE,
    RESOURCE_KEANIUM_HYDRIDE,
    RESOURCE_UTRIUM_OXIDE,
    RESOURCE_UTRIUM_HYDRIDE,
    RESOURCE_UTRIUM_LEMERGITE,
    RESOURCE_ZYNTHIUM_KEANITE,
    RESOURCE_HYDROXIDE,
    RESOURCE_GHODIUM,
    RESOURCE_CATALYST,
    RESOURCE_ZYNTHIUM,
    RESOURCE_LEMERGIUM,
    RESOURCE_KEANIUM,
    RESOURCE_UTRIUM,
    RESOURCE_OXYGEN,
    RESOURCE_HYDROGEN,
    RESOURCE_ENERGY,
];
const REAGENTS = {
    // Tier 3
    [RESOURCE_CATALYZED_GHODIUM_ALKALIDE]: [RESOURCE_GHODIUM_ALKALIDE, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_GHODIUM_ACID]: [RESOURCE_GHODIUM_ACID, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_ZYNTHIUM_ACID]: [RESOURCE_ZYNTHIUM_ACID, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_ZYNTHIUM_ALKALIDE]: [RESOURCE_ZYNTHIUM_ALKALIDE, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_LEMERGIUM_ALKALIDE]: [RESOURCE_LEMERGIUM_ALKALIDE, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_LEMERGIUM_ACID]: [RESOURCE_LEMERGIUM_ACID, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_KEANIUM_ALKALIDE]: [RESOURCE_KEANIUM_ALKALIDE, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_KEANIUM_ACID]: [RESOURCE_KEANIUM_ACID, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_UTRIUM_ACID]: [RESOURCE_UTRIUM_ACID, RESOURCE_CATALYST],
    [RESOURCE_CATALYZED_UTRIUM_ALKALIDE]: [RESOURCE_UTRIUM_ALKALIDE, RESOURCE_CATALYST],
    // Tier 2
    [RESOURCE_GHODIUM_ACID]: [RESOURCE_GHODIUM_HYDRIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_GHODIUM_ALKALIDE]: [RESOURCE_GHODIUM_OXIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_ZYNTHIUM_ACID]: [RESOURCE_ZYNTHIUM_HYDRIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_ZYNTHIUM_ALKALIDE]: [RESOURCE_ZYNTHIUM_OXIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_LEMERGIUM_ALKALIDE]: [RESOURCE_LEMERGIUM_OXIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_LEMERGIUM_ACID]: [RESOURCE_LEMERGIUM_HYDRIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_KEANIUM_ALKALIDE]: [RESOURCE_KEANIUM_OXIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_KEANIUM_ACID]: [RESOURCE_KEANIUM_HYDRIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_UTRIUM_ACID]: [RESOURCE_UTRIUM_HYDRIDE, RESOURCE_HYDROXIDE],
    [RESOURCE_UTRIUM_ALKALIDE]: [RESOURCE_UTRIUM_OXIDE, RESOURCE_HYDROXIDE],
    // Tier 1
    [RESOURCE_GHODIUM_HYDRIDE]: [RESOURCE_GHODIUM, RESOURCE_HYDROGEN],
    [RESOURCE_GHODIUM_OXIDE]: [RESOURCE_GHODIUM, RESOURCE_OXYGEN],
    [RESOURCE_ZYNTHIUM_HYDRIDE]: [RESOURCE_ZYNTHIUM, RESOURCE_HYDROGEN],
    [RESOURCE_ZYNTHIUM_OXIDE]: [RESOURCE_ZYNTHIUM, RESOURCE_OXYGEN],
    [RESOURCE_LEMERGIUM_OXIDE]: [RESOURCE_LEMERGIUM, RESOURCE_OXYGEN],
    [RESOURCE_LEMERGIUM_HYDRIDE]: [RESOURCE_LEMERGIUM, RESOURCE_HYDROGEN],
    [RESOURCE_KEANIUM_OXIDE]: [RESOURCE_KEANIUM, RESOURCE_OXYGEN],
    [RESOURCE_KEANIUM_HYDRIDE]: [RESOURCE_KEANIUM, RESOURCE_HYDROGEN],
    [RESOURCE_UTRIUM_HYDRIDE]: [RESOURCE_UTRIUM, RESOURCE_HYDROGEN],
    [RESOURCE_UTRIUM_OXIDE]: [RESOURCE_UTRIUM, RESOURCE_OXYGEN],
    // Tier 0
    [RESOURCE_GHODIUM]: [RESOURCE_ZYNTHIUM_KEANITE, RESOURCE_UTRIUM_LEMERGITE],
    [RESOURCE_HYDROXIDE]: [RESOURCE_OXYGEN, RESOURCE_HYDROGEN],
    [RESOURCE_ZYNTHIUM_KEANITE]: [RESOURCE_ZYNTHIUM, RESOURCE_KEANIUM],
    [RESOURCE_UTRIUM_LEMERGITE]: [RESOURCE_UTRIUM, RESOURCE_LEMERGIUM]
};
const boostParts = {
    'UH': ATTACK,
    'UO': WORK,
    'KH': CARRY,
    'KO': RANGED_ATTACK,
    'LH': WORK,
    'LO': HEAL,
    'ZH': WORK,
    'ZO': MOVE,
    'GH': WORK,
    'GO': TOUGH,
    'UH2O': ATTACK,
    'UHO2': WORK,
    'KH2O': CARRY,
    'KHO2': RANGED_ATTACK,
    'LH2O': WORK,
    'LHO2': HEAL,
    'ZH2O': WORK,
    'ZHO2': MOVE,
    'GH2O': WORK,
    'GHO2': TOUGH,
    'XUH2O': ATTACK,
    'XUHO2': WORK,
    'XKH2O': CARRY,
    'XKHO2': RANGED_ATTACK,
    'XLH2O': WORK,
    'XLHO2': HEAL,
    'XZH2O': WORK,
    'XZHO2': MOVE,
    'XGH2O': WORK,
    'XGHO2': TOUGH,
};
const boostResources = {
    'attack': {
        1: 'UH',
        2: 'UH2O',
        3: 'XUH2O',
    },
    'carry': {
        1: 'KH',
        2: 'KH2O',
        3: 'XKH2O',
    },
    'ranged_attack': {
        1: 'KO',
        2: 'KHO2',
        3: 'XKHO2',
    },
    'heal': {
        1: 'LO',
        2: 'LHO2',
        3: 'XLHO2',
    },
    'move': {
        1: 'ZO',
        2: 'ZHO2',
        3: 'XZHO2',
    },
    'tough': {
        1: 'GO',
        2: 'GHO2',
        3: 'XGHO2',
    },
    'harvest': {
        1: 'UO',
        2: 'UHO2',
        3: 'XUHO2',
    },
    'construct': {
        1: 'LH',
        2: 'LH2O',
        3: 'XLH2O',
    },
    'dismantle': {
        1: 'ZH',
        2: 'ZH2O',
        3: 'XZH2O',
    },
    'upgrade': {
        1: 'GH',
        2: 'GH2O',
        3: 'XGH2O',
    },
};

const getBoostedTaskName = 'getBoosted';
const MIN_LIFETIME_FOR_BOOST = 0.85;
let TaskGetBoosted = class TaskGetBoosted extends Task {
    constructor(target, boostType, partCount = undefined, options = {}) {
        super(getBoostedTaskName, target, options);
        // Settings
        this.data.resourceType = boostType;
        this.data.amount = partCount;
    }
    isValidTask() {
        let lifetime = _.any(this.creep.body, part => part.type == CLAIM) ? CREEP_CLAIM_LIFE_TIME : CREEP_LIFE_TIME;
        if (this.creep.ticksToLive && this.creep.ticksToLive < MIN_LIFETIME_FOR_BOOST * lifetime) {
            return false; // timeout after this amount of lifespan has passed
        }
        let partCount = (this.data.amount || this.creep.getActiveBodyparts(boostParts[this.data.resourceType]));
        return (this.creep.boostCounts[this.data.resourceType] || 0) < partCount;
    }
    isValidTarget() {
        let partCount = (this.data.amount || this.creep.getActiveBodyparts(boostParts[this.data.resourceType]));
        return this.target && this.target.mineralType == this.data.resourceType &&
            this.target.mineralAmount >= LAB_BOOST_MINERAL * partCount &&
            this.target.energy >= LAB_BOOST_ENERGY * partCount;
    }
    work() {
        if (this.creep.spawning) {
            return ERR_INVALID_TARGET;
        }
        let partCount = (this.data.amount || this.creep.getActiveBodyparts(boostParts[this.data.resourceType]));
        if (this.target.mineralType == this.data.resourceType &&
            this.target.mineralAmount >= LAB_BOOST_MINERAL * partCount &&
            this.target.energy >= LAB_BOOST_ENERGY * partCount) {
            let result = this.target.boostCreep(deref(this._creep.name), this.data.amount);
            log.info(`Lab@${this.target.pos.print}: boosting creep ${this.creep.print} with ${this.target.mineralType}!`
                + ` Response: ${result}`);
            return result;
        }
        else {
            return ERR_NOT_FOUND;
        }
    }
};
TaskGetBoosted = __decorate([
    profile
], TaskGetBoosted);

const getRenewedTaskName = 'getRenewed';
let TaskGetRenewed = class TaskGetRenewed extends Task {
    constructor(target, options = {}) {
        super(getRenewedTaskName, target, options);
    }
    isValidTask() {
        let hasClaimPart = _.filter(this.creep.body, (part) => part.type == CLAIM).length > 0;
        let lifetime = hasClaimPart ? CREEP_CLAIM_LIFE_TIME : CREEP_LIFE_TIME;
        return this.creep.ticksToLive != undefined && this.creep.ticksToLive < 0.9 * lifetime;
    }
    isValidTarget() {
        return this.target.my && !this.target.spawning;
    }
    work() {
        return this.target.renewCreep(this.creep.creep);
    }
};
TaskGetRenewed = __decorate([
    profile
], TaskGetRenewed);

// Type guards library: this allows for instanceof - like behavior for much lower CPU cost. Each type guard
// differentiates an ambiguous input by recognizing one or more unique properties.
function isEnergyStructure(obj) {
    return obj.energy != undefined && obj.energyCapacity != undefined;
}
function isStoreStructure(obj) {
    return obj.store != undefined && obj.storeCapacity != undefined;
}
function isStructure(obj) {
    return obj.structureType != undefined;
}
function isOwnedStructure(structure) {
    return structure.owner != undefined;
}
function isSource(obj) {
    return obj.energy != undefined;
}
function isTombstone(obj) {
    return obj.deathTime != undefined;
}
function isResource(obj) {
    return obj.amount != undefined;
}
function hasPos(obj) {
    return obj.pos != undefined;
}
function isCreep(obj) {
    return obj.fatigue != undefined;
}
function isZerg(creep) {
    return creep.creep != undefined;
}
function isCombatZerg(zerg) {
    return zerg.isCombatZerg != undefined;
}

const goToTaskName = 'goTo';
let TaskGoTo = class TaskGoTo extends Task {
    constructor(target, options = {}) {
        if (hasPos(target)) {
            super(goToTaskName, { ref: '', pos: target.pos }, options);
        }
        else {
            super(goToTaskName, { ref: '', pos: target }, options);
        }
        // Settings
        this.settings.targetRange = 1;
    }
    isValidTask() {
        return !this.creep.pos.inRangeTo(this.targetPos, this.settings.targetRange);
    }
    isValidTarget() {
        return true;
    }
    isValid() {
        let validTask = false;
        if (this.creep) {
            validTask = this.isValidTask();
        }
        // Return if the task is valid; if not, finalize/delete the task and return false
        if (validTask) {
            return true;
        }
        else {
            // Switch to parent task if there is one
            let isValid = false;
            if (this.parent) {
                isValid = this.parent.isValid();
            }
            this.finish();
            return isValid;
        }
    }
    work() {
        return OK;
    }
};
TaskGoTo = __decorate([
    profile
], TaskGoTo);

const goToRoomTaskName = 'goToRoom';
let TaskGoToRoom = class TaskGoToRoom extends Task {
    constructor(roomName, options = {}) {
        super(goToRoomTaskName, { ref: '', pos: new RoomPosition(25, 25, roomName) }, options);
        // Settings
        this.settings.targetRange = 23; // Target is almost always controller flag, so range of 2 is acceptable
    }
    isValidTask() {
        return !this.creep.pos.inRangeTo(this.targetPos, this.settings.targetRange);
    }
    isValidTarget() {
        return true;
    }
    isValid() {
        let validTask = false;
        if (this.creep) {
            validTask = this.isValidTask();
        }
        // Return if the task is valid; if not, finalize/delete the task and return false
        if (validTask) {
            return true;
        }
        else {
            // Switch to parent task if there is one
            let isValid = false;
            if (this.parent) {
                isValid = this.parent.isValid();
            }
            this.finish();
            return isValid;
        }
    }
    work() {
        return OK;
    }
};
TaskGoToRoom = __decorate([
    profile
], TaskGoToRoom);

const harvestTaskName = 'harvest';
let TaskHarvest = class TaskHarvest extends Task {
    constructor(target, options = {}) {
        super(harvestTaskName, target, options);
    }
    isValidTask() {
        return _.sum(this.creep.carry) < this.creep.carryCapacity;
    }
    isValidTarget() {
        if (isSource(this.target)) {
            return this.target.energy > 0;
        }
        else {
            return this.target.mineralAmount > 0;
        }
    }
    work() {
        return this.creep.harvest(this.target);
    }
};
TaskHarvest = __decorate([
    profile
], TaskHarvest);

const healTaskName = 'heal';
let TaskHeal = class TaskHeal extends Task {
    constructor(target, options = {}) {
        super(healTaskName, target, options);
        // Settings
        this.settings.targetRange = 3;
    }
    isValidTask() {
        return (this.creep.getActiveBodyparts(HEAL) > 0);
    }
    isValidTarget() {
        return this.target && this.target.hits < this.target.hitsMax && this.target.my;
    }
    work() {
        if (this.creep.pos.isNearTo(this.target)) {
            return this.creep.heal(this.target);
        }
        else {
            this.moveToTarget(1);
        }
        return this.creep.rangedHeal(this.target);
    }
};
TaskHeal = __decorate([
    profile
], TaskHeal);

const meleeAttackTaskName = 'meleeAttack';
let TaskMeleeAttack = class TaskMeleeAttack extends Task {
    constructor(target, options = {}) {
        super(meleeAttackTaskName, target, options);
        // Settings
        this.settings.targetRange = 1;
    }
    isValidTask() {
        return this.creep.getActiveBodyparts(ATTACK) > 0;
    }
    isValidTarget() {
        var target = this.target;
        return target && target.hits > 0; // && target.my == false);
    }
    work() {
        return this.creep.attack(this.target);
    }
};
TaskMeleeAttack = __decorate([
    profile
], TaskMeleeAttack);

const pickupTaskName = 'pickup';
let TaskPickup = class TaskPickup extends Task {
    constructor(target, options = {}) {
        super('pickup', target, options);
        this.settings.oneShot = true;
    }
    isValidTask() {
        return _.sum(this.creep.carry) < this.creep.carryCapacity;
    }
    isValidTarget() {
        return this.target && this.target.amount > 0;
    }
    work() {
        return this.creep.pickup(this.target);
    }
};
TaskPickup = __decorate([
    profile
], TaskPickup);

const rangedAttackTaskName = 'rangedAttack';
let TaskRangedAttack = class TaskRangedAttack extends Task {
    constructor(target, options = {}) {
        super(rangedAttackTaskName, target, options);
        // Settings
        this.settings.targetRange = 3;
    }
    isValidTask() {
        return this.creep.getActiveBodyparts(RANGED_ATTACK) > 0;
    }
    isValidTarget() {
        return this.target && this.target.hits > 0;
    }
    work() {
        return this.creep.rangedAttack(this.target);
    }
};
TaskRangedAttack = __decorate([
    profile
], TaskRangedAttack);

/* Withdraw a resource from a target */
const withdrawTaskName = 'withdraw';
let TaskWithdraw = class TaskWithdraw extends Task {
    constructor(target, resourceType = RESOURCE_ENERGY, amount = undefined, options = {}) {
        super(withdrawTaskName, target, options);
        // Settings
        this.settings.oneShot = true;
        this.data.resourceType = resourceType;
        this.data.amount = amount;
    }
    isValidTask() {
        let amount = this.data.amount || 1;
        return (_.sum(this.creep.carry) <= this.creep.carryCapacity - amount);
    }
    isValidTarget() {
        let amount = this.data.amount || 1;
        let target = this.target;
        if (target instanceof Tombstone || isStoreStructure(target)) {
            return (target.store[this.data.resourceType] || 0) >= amount;
        }
        else if (isEnergyStructure(target) && this.data.resourceType == RESOURCE_ENERGY) {
            return target.energy >= amount;
        }
        else {
            if (target instanceof StructureLab) {
                return this.data.resourceType == target.mineralType && target.mineralAmount >= amount;
            }
            else if (target instanceof StructurePowerSpawn) {
                return this.data.resourceType == RESOURCE_POWER && target.power >= amount;
            }
        }
        return false;
    }
    work() {
        return this.creep.withdraw(this.target, this.data.resourceType, this.data.amount);
    }
};
TaskWithdraw = __decorate([
    profile
], TaskWithdraw);

const repairTaskName = 'repair';
let TaskRepair = class TaskRepair extends Task {
    constructor(target, options = {}) {
        super(repairTaskName, target, options);
        // Settings
        this.settings.timeout = 100;
        this.settings.targetRange = 3;
    }
    isValidTask() {
        return this.creep.carry.energy > 0;
    }
    isValidTarget() {
        return this.target && this.target.hits < this.target.hitsMax;
    }
    work() {
        let result = this.creep.repair(this.target);
        if (this.target.structureType == STRUCTURE_ROAD) {
            // prevents workers from idling for a tick before moving to next target
            let newHits = this.target.hits + this.creep.getActiveBodyparts(WORK) * REPAIR_POWER;
            if (newHits > this.target.hitsMax) {
                this.finish();
            }
        }
        return result;
    }
};
TaskRepair = __decorate([
    profile
], TaskRepair);

const reserveTaskName = 'colony';
let TaskReserve = class TaskReserve extends Task {
    constructor(target, options = {}) {
        super(reserveTaskName, target, options);
    }
    isValidTask() {
        return (this.creep.getActiveBodyparts(CLAIM) > 0);
    }
    isValidTarget() {
        var target = this.target;
        return (target != null && (!target.reservation || target.reservation.ticksToEnd < 4999));
    }
    work() {
        return this.creep.reserveController(this.target);
    }
};
TaskReserve = __decorate([
    profile
], TaskReserve);

const signControllerTaskName = 'signController';
let TaskSignController = class TaskSignController extends Task {
    constructor(target, options = {}) {
        super(signControllerTaskName, target, options);
    }
    isValidTask() {
        return true;
    }
    isValidTarget() {
        let controller = this.target;
        return (!controller.sign || controller.sign.text != Memory.settings.signature) && !controller.signedByScreeps;
    }
    work() {
        return this.creep.signController(this.target, Memory.settings.signature);
    }
};
TaskSignController = __decorate([
    profile
], TaskSignController);

const transferTaskName = 'transfer';
let TaskTransfer = class TaskTransfer extends Task {
    constructor(target, resourceType = RESOURCE_ENERGY, amount = undefined, options = {}) {
        super(transferTaskName, target, options);
        // Settings
        this.settings.oneShot = true;
        this.data.resourceType = resourceType;
        this.data.amount = amount;
    }
    isValidTask() {
        let amount = this.data.amount || 1;
        let resourcesInCarry = this.creep.carry[this.data.resourceType] || 0;
        return resourcesInCarry >= amount;
    }
    isValidTarget() {
        let amount = this.data.amount || 1;
        let target = this.target;
        if (target instanceof Creep) {
            return _.sum(target.carry) <= target.carryCapacity - amount;
        }
        else if (isStoreStructure(target)) {
            return _.sum(target.store) <= target.storeCapacity - amount;
        }
        else if (isEnergyStructure(target) && this.data.resourceType == RESOURCE_ENERGY) {
            return target.energy <= target.energyCapacity - amount;
        }
        else {
            if (target instanceof StructureLab) {
                return (target.mineralType == this.data.resourceType || !target.mineralType) &&
                    target.mineralAmount <= target.mineralCapacity - amount;
            }
            else if (target instanceof StructureNuker) {
                return this.data.resourceType == RESOURCE_GHODIUM &&
                    target.ghodium <= target.ghodiumCapacity - amount;
            }
            else if (target instanceof StructurePowerSpawn) {
                return this.data.resourceType == RESOURCE_POWER &&
                    target.power <= target.powerCapacity - amount;
            }
        }
        return false;
    }
    work() {
        return this.creep.transfer(this.target, this.data.resourceType, this.data.amount);
    }
};
TaskTransfer = __decorate([
    profile
], TaskTransfer);

const upgradeTaskName = 'upgrade';
let TaskUpgrade = class TaskUpgrade extends Task {
    constructor(target, options = {}) {
        super(upgradeTaskName, target, options);
        // Settings
        this.settings.targetRange = 3;
        this.settings.workOffRoad = true;
    }
    isValidTask() {
        return (this.creep.carry.energy > 0);
    }
    isValidTarget() {
        return this.target && this.target.my;
    }
    work() {
        return this.creep.upgradeController(this.target);
    }
};
TaskUpgrade = __decorate([
    profile
], TaskUpgrade);

var TaskDrop_1;
const dropTaskName = 'drop';
let TaskDrop = TaskDrop_1 = class TaskDrop extends Task {
    constructor(target, resourceType = RESOURCE_ENERGY, amount = undefined, options = {}) {
        if (target instanceof RoomPosition) {
            super(TaskDrop_1.taskName, { ref: '', pos: target }, options);
        }
        else {
            super(TaskDrop_1.taskName, { ref: '', pos: target.pos }, options);
        }
        // Settings
        this.settings.targetRange = 0;
        this.settings.oneShot = true;
        // Data
        this.data.resourceType = resourceType;
        this.data.amount = amount;
    }
    isValidTask() {
        let amount = this.data.amount || 1;
        let resourcesInCarry = this.creep.carry[this.data.resourceType] || 0;
        return resourcesInCarry >= amount;
    }
    isValidTarget() {
        return true;
    }
    isValid() {
        // It's necessary to override task.isValid() for tasks which do not have a RoomObject target
        let validTask = false;
        if (this.creep) {
            validTask = this.isValidTask();
        }
        // Return if the task is valid; if not, finalize/delete the task and return false
        if (validTask) {
            return true;
        }
        else {
            // Switch to parent task if there is one
            let isValid = false;
            if (this.parent) {
                isValid = this.parent.isValid();
            }
            this.finish();
            return isValid;
        }
    }
    work() {
        return this.creep.drop(this.data.resourceType, this.data.amount);
    }
};
TaskDrop.taskName = 'drop';
TaskDrop = TaskDrop_1 = __decorate([
    profile
], TaskDrop);

// Invalid task assigned if instantiation fails.
const invalidTarget = {
    ref: '',
    pos: {
        x: 25,
        y: 25,
        roomName: 'W6N1',
    }
};
let TaskInvalid = class TaskInvalid extends Task {
    constructor() {
        super('INVALID', invalidTarget);
    }
    isValidTask() {
        return false;
    }
    isValidTarget() {
        return false;
    }
    work() {
        return OK;
    }
};
TaskInvalid = __decorate([
    profile
], TaskInvalid);

const transferAllTaskName = 'transferAll';
let TaskTransferAll = class TaskTransferAll extends Task {
    constructor(target, skipEnergy = false, options = {}) {
        super(transferAllTaskName, target, options);
        this.data.skipEnergy = skipEnergy;
    }
    isValidTask() {
        for (let resourceType in this.creep.carry) {
            if (this.data.skipEnergy && resourceType == RESOURCE_ENERGY) {
                continue;
            }
            let amountInCarry = this.creep.carry[resourceType] || 0;
            if (amountInCarry > 0) {
                return true;
            }
        }
        return false;
    }
    isValidTarget() {
        return _.sum(this.target.store) < this.target.storeCapacity;
    }
    work() {
        for (let resourceType in this.creep.carry) {
            if (this.data.skipEnergy && resourceType == RESOURCE_ENERGY) {
                continue;
            }
            let amountInCarry = this.creep.carry[resourceType] || 0;
            if (amountInCarry > 0) {
                return this.creep.transfer(this.target, resourceType);
            }
        }
        return -1;
    }
};
TaskTransferAll = __decorate([
    profile
], TaskTransferAll);

/* Withdraw a resource from a target */
const withdrawAllTaskName = 'withdrawAll';
let TaskWithdrawAll = class TaskWithdrawAll extends Task {
    constructor(target, options = {}) {
        super(withdrawAllTaskName, target, options);
    }
    isValidTask() {
        return (_.sum(this.creep.carry) < this.creep.carryCapacity);
    }
    isValidTarget() {
        return _.sum(this.target.store) > 0;
    }
    work() {
        for (let resourceType in this.target.store) {
            let amountInStore = this.target.store[resourceType] || 0;
            if (amountInStore > 0) {
                return this.creep.withdraw(this.target, resourceType);
            }
        }
        return -1;
    }
};
TaskWithdrawAll = __decorate([
    profile
], TaskWithdrawAll);

const rechargeTaskName = 'recharge';
// This is a "dispenser task" which is not itself a valid task, but dispenses a task when assigned to a creep.
let TaskRecharge = class TaskRecharge extends Task {
    constructor(target, minEnergy = 0, options = {}) {
        super(rechargeTaskName, { ref: '', pos: { x: -1, y: -1, roomName: '' } }, options);
        this.data.minEnergy = minEnergy;
    }
    rechargeRateForCreep(creep, obj) {
        if (creep.colony.hatchery && creep.colony.hatchery.battery
            && obj.id == creep.colony.hatchery.battery.id && creep.roleName != 'queen') {
            return false; // only queens can use the hatchery battery
        }
        let amount = isResource(obj) ? obj.amount : obj.energy;
        if (amount < this.data.minEnergy) {
            return false;
        }
        const otherTargeters = _.filter(_.map(obj.targetedBy, name => Overmind.zerg[name]), zerg => !!zerg && zerg.memory._task
            && (zerg.memory._task.name == withdrawTaskName
                || zerg.memory._task.name == pickupTaskName));
        const resourceOutflux = _.sum(_.map(otherTargeters, other => other.carryCapacity - _.sum(other.carry)));
        amount = minMax(amount - resourceOutflux, 0, creep.carryCapacity);
        let effectiveAmount = amount / (creep.pos.getMultiRoomRangeTo(obj.pos) + 1);
        if (effectiveAmount <= 0) {
            return false;
        }
        else {
            return effectiveAmount;
        }
    }
    // Override creep setter to dispense a valid recharge task
    set creep(creep) {
        this._creep.name = creep.name;
        if (this._parent) {
            this.parent.creep = creep;
        }
        // Choose the target to maximize your energy gain subject to other targeting workers
        let target = creep.inColonyRoom ? maxBy(creep.colony.rechargeables, o => this.rechargeRateForCreep(creep, o))
            : maxBy(creep.room.rechargeables, o => this.rechargeRateForCreep(creep, o));
        if (!target || creep.pos.getMultiRoomRangeTo(target.pos) > 40) {
            // workers shouldn't harvest; let drones do it (disabling this check can destabilize early economy)
            let canHarvest = creep.getActiveBodyparts(WORK) > 0 && creep.roleName != 'worker';
            if (canHarvest) {
                // Harvest from a source if there is no recharge target available
                let availableSources = _.filter(creep.room.sources, function (source) {
                    // Only harvest from sources which aren't surrounded by creeps excluding yourself
                    let isSurrounded = source.pos.availableNeighbors(false).length == 0;
                    return !isSurrounded || creep.pos.isNearTo(source);
                });
                let availableSource = creep.pos.findClosestByMultiRoomRange(availableSources);
                if (availableSource) {
                    creep.task = new TaskHarvest(availableSource);
                    return;
                }
            }
        }
        if (target) {
            if (isResource(target)) {
                creep.task = new TaskPickup(target);
                return;
            }
            else {
                creep.task = new TaskWithdraw(target);
                return;
            }
        }
        else {
            // if (creep.roleName == 'queen') {
            log.debug(`No valid withdraw target for ${creep.print}!`);
            // }
            creep.task = null;
        }
    }
    isValidTask() {
        return false;
    }
    isValidTarget() {
        return false;
    }
    work() {
        log.warning(`BAD RESULT: Should not get here...`);
        return ERR_INVALID_TARGET;
    }
};
TaskRecharge = __decorate([
    profile
], TaskRecharge);

function initializeTask(protoTask) {
    // Retrieve name and target data from the protoTask
    let taskName = protoTask.name;
    let target = deref(protoTask._target.ref);
    let task;
    // Create a task object of the correct type
    switch (taskName) {
        case attackTaskName:
            task = new TaskAttack(target);
            break;
        case buildTaskName:
            task = new TaskBuild(target);
            break;
        case claimTaskName:
            task = new TaskClaim(target);
            break;
        case dismantleTaskName:
            task = new TaskDismantle(target);
            break;
        case dropTaskName:
            task = new TaskDrop(derefRoomPosition(protoTask._target._pos));
            break;
        // case fleeTaskName:
        // 	task = new TaskFlee(derefRoomPosition(protoTask._target._pos) as fleeTargetType);
        // 	break;
        case fortifyTaskName:
            task = new TaskFortify(target);
            break;
        case getBoostedTaskName:
            task = new TaskGetBoosted(target, protoTask.data.resourceType);
            break;
        case getRenewedTaskName:
            task = new TaskGetRenewed(target);
            break;
        case goToTaskName:
            // task = new TaskGoTo(derefRoomPosition(protoTask._target._pos) as goToTargetType);
            task = new TaskInvalid();
            break;
        case goToRoomTaskName:
            task = new TaskGoToRoom(protoTask._target._pos.roomName);
            break;
        case harvestTaskName:
            task = new TaskHarvest(target);
            break;
        case healTaskName:
            task = new TaskHeal(target);
            break;
        case meleeAttackTaskName:
            task = new TaskMeleeAttack(target);
            break;
        case pickupTaskName:
            task = new TaskPickup(target);
            break;
        case rangedAttackTaskName:
            task = new TaskRangedAttack(target);
            break;
        case rechargeTaskName:
            task = new TaskRecharge(null);
            break;
        case repairTaskName:
            task = new TaskRepair(target);
            break;
        case reserveTaskName:
            task = new TaskReserve(target);
            break;
        case signControllerTaskName:
            task = new TaskSignController(target);
            break;
        case transferTaskName:
            task = new TaskTransfer(target);
            break;
        case transferAllTaskName:
            task = new TaskTransferAll(target);
            break;
        case upgradeTaskName:
            task = new TaskUpgrade(target);
            break;
        case withdrawTaskName:
            task = new TaskWithdraw(target);
            break;
        case withdrawAllTaskName:
            task = new TaskWithdrawAll(target);
            break;
        default:
            log.error(`Invalid task name: ${taskName}! task.creep: ${protoTask._creep.name}. Deleting from memory!`);
            task = new TaskInvalid();
            break;
    }
    // Modify the task object to reflect any changed properties
    task.proto = protoTask;
    // Return it
    return task;
}
screepsProfiler.registerFN(initializeTask, 'initializeTask');

/* Returns destination.pos if destination has a position, or destination if destination is a RoomPosition */
function normalizePos(destination) {
    if (hasPos(destination)) {
        return destination.pos;
    }
    else {
        return destination;
    }
}
/* Returns if the coordinate is on an exit tile */
function isExit(pos) {
    return pos.x == 0 || pos.y == 0 || pos.x == 49 || pos.y == 49;
}
/* Checks if the coordinates of two room positions are the same */
function sameCoord(pos1, pos2) {
    return pos1.x == pos2.x && pos1.y == pos2.y;
}
/* Returns the number of move parts and number of weight-generating parts in a creep */
function getCreepWeightInfo(creep, analyzeCarry = true) {
    // Compute number of weighted and unweighted bodyparts
    const unweightedParts = analyzeCarry ? [MOVE, CARRY] : [MOVE];
    const bodyParts = _.countBy(creep.body, p => _.contains(unweightedParts, p.type) ? p.type : 'weighted');
    bodyParts.move = bodyParts.move || 0;
    bodyParts.weighted = bodyParts.weighted || 0;
    if (bodyParts[CARRY]) {
        bodyParts.weighted += Math.ceil(_.sum(creep.carry) / CARRY_CAPACITY);
    }
    // Account for boosts
    for (let part of creep.body) {
        if (part.type == MOVE && part.boost) {
            bodyParts.move += (BOOSTS.move[part.boost].fatigue - 1);
        }
    }
    return bodyParts;
}
function getTerrainCosts(creep) {
    const data = getCreepWeightInfo(creep);
    const ratio = data.weighted / data.move;
    return {
        plainCost: Math.ceil(ratio),
        swampCost: 5 * Math.ceil(ratio),
    };
}

const CACHE_TIMEOUT = 50;
const SHORT_CACHE_TIMEOUT = 10;
let $ = class $ {
    static structures(saver, key, callback, timeout = CACHE_TIMEOUT) {
        const cacheKey = saver.ref + 's' + key;
        if (!_cache.structures[cacheKey] || Game.time > _cache.expiration[cacheKey]) {
            // Recache if new entry or entry is expired
            _cache.structures[cacheKey] = callback();
            _cache.expiration[cacheKey] = getCacheExpiration(timeout, Math.ceil(timeout / 10));
        }
        else {
            // Refresh structure list by ID if not already done on current tick
            if ((_cache.accessed[cacheKey] || 0) < Game.time) {
                _cache.structures[cacheKey] = _.compact(_.map(_cache.structures[cacheKey] || [], s => Game.getObjectById(s.id)));
                _cache.accessed[cacheKey] = Game.time;
            }
        }
        return _cache.structures[cacheKey];
    }
    static number(saver, key, callback, timeout = SHORT_CACHE_TIMEOUT) {
        const cacheKey = saver.ref + '#' + key;
        if (_cache.numbers[cacheKey] == undefined || Game.time > _cache.expiration[cacheKey]) {
            // Recache if new entry or entry is expired
            _cache.numbers[cacheKey] = callback();
            _cache.expiration[cacheKey] = getCacheExpiration(timeout, Math.ceil(timeout / 10));
        }
        return _cache.numbers[cacheKey];
    }
    // TODO: for some reason overloading isn't working here...
    // static pos(saver: { ref: string }, key: string, callback: () => RoomPosition, timeout ?: number): RoomPosition;
    static pos(saver, key, callback, timeout) {
        const cacheKey = saver.ref + 'p' + key;
        if (_cache.roomPositions[cacheKey] == undefined || Game.time > _cache.expiration[cacheKey]) {
            // Recache if new entry or entry is expired
            _cache.roomPositions[cacheKey] = callback();
            if (!timeout)
                timeout = CACHE_TIMEOUT;
            _cache.expiration[cacheKey] = getCacheExpiration(timeout, Math.ceil(timeout / 10));
        }
        return _cache.roomPositions[cacheKey];
    }
    static list(saver, key, callback, timeout = CACHE_TIMEOUT) {
        const cacheKey = saver.ref + 'l' + key;
        if (_cache.lists[cacheKey] == undefined || Game.time > _cache.expiration[cacheKey]) {
            // Recache if new entry or entry is expired
            _cache.lists[cacheKey] = callback();
            _cache.expiration[cacheKey] = getCacheExpiration(timeout, Math.ceil(timeout / 10));
        }
        return _cache.lists[cacheKey];
    }
    static costMatrix(roomName, key, callback, timeout = SHORT_CACHE_TIMEOUT) {
        const cacheKey = roomName + 'm' + key;
        if (_cache.costMatrices[cacheKey] == undefined || Game.time > _cache.expiration[cacheKey]) {
            // Recache if new entry or entry is expired
            _cache.costMatrices[cacheKey] = callback();
            _cache.expiration[cacheKey] = getCacheExpiration(timeout, Math.ceil(timeout / 10));
        }
        return _cache.costMatrices[cacheKey];
    }
    static costMatrixRecall(roomName, key) {
        let cacheKey = roomName + ':' + key;
        return _cache.costMatrices[cacheKey];
    }
    static set(thing, key, callback, timeout = CACHE_TIMEOUT) {
        const cacheKey = thing.ref + '$' + key;
        if (!_cache.things[cacheKey] || Game.time > _cache.expiration[cacheKey]) {
            // Recache if new entry or entry is expired
            _cache.things[cacheKey] = callback();
            _cache.expiration[cacheKey] = getCacheExpiration(timeout, Math.ceil(timeout / 10));
        }
        else {
            // Refresh structure list by ID if not already done on current tick
            if ((_cache.accessed[cacheKey] || 0) < Game.time) {
                if (_.isArray(_cache.things[cacheKey])) {
                    _cache.things[cacheKey] = _.compact(_.map(_cache.things[cacheKey], s => Game.getObjectById(s.id)));
                }
                else {
                    _cache.things[cacheKey] = Game.getObjectById(_cache.things[cacheKey].id);
                }
                _cache.accessed[cacheKey] = Game.time;
            }
        }
        thing[key] = _cache.things[cacheKey];
    }
    static refresh(thing, ...keys) {
        _.forEach(keys, function (key) {
            if (thing[key]) {
                if (_.isArray(thing[key])) {
                    thing[key] = _.compact(_.map(thing[key], s => Game.getObjectById(s.id)));
                }
                else {
                    thing[key] = Game.getObjectById(thing[key].id);
                }
            }
        });
    }
    static refreshObject(thing, ...keys) {
        _.forEach(keys, function (key) {
            if (_.isObject(thing[key])) {
                for (let prop in thing[key]) {
                    if (_.isArray(thing[key][prop])) {
                        thing[key][prop] = _.compact(_.map(thing[key][prop], s => Game.getObjectById(s.id)));
                    }
                    else {
                        thing[key][prop] = Game.getObjectById(thing[key][prop].id);
                    }
                }
            }
        });
    }
    static refreshRoom(thing) {
        thing.room = Game.rooms[thing.room.name];
    }
};
$ = __decorate([
    profile
], $);

var Pathing_1;
/* Module for pathing-related operations. */
const DEFAULT_MAXOPS = 20000; // Default timeout for pathfinding
const CREEP_COST = 0xfe;
const MatrixTypes = {
    direct: 'dir',
    default: 'def',
    sk: 'sk',
    obstacle: 'obst',
    preferRampart: 'preframp'
};
let Pathing = Pathing_1 = class Pathing {
    // Room avoidance methods ==========================================================================================
    /* Check if the room should be avoiding when calculating routes */
    static shouldAvoid(roomName) {
        return Memory.rooms[roomName] && Memory.rooms[roomName].avoid;
    }
    /* Update memory on whether a room should be avoided based on controller owner */
    static updateRoomStatus(room) {
        if (!room) {
            return;
        }
        if (room.controller) {
            if (room.controller.owner && !room.controller.my && room.towers.length > 0) {
                room.memory.avoid = true;
            }
            else {
                delete room.memory.avoid;
                // if (room.memory.expansionData == false) delete room.memory.expansionData;
            }
        }
    }
    // Pathfinding and room callback methods ===========================================================================
    /* Find a path from origin to destination */
    static findPath(origin, destination, options = {}) {
        _.defaults(options, {
            ignoreCreeps: true,
            maxOps: DEFAULT_MAXOPS,
            range: 1,
            terrainCosts: { plainCost: 1, swampCost: 5 },
        });
        if (options.movingTarget) {
            options.range = 0;
        }
        // check to see whether findRoute should be used
        let roomDistance = Game.map.getRoomLinearDistance(origin.roomName, destination.roomName);
        let allowedRooms = options.route;
        if (!allowedRooms && (options.useFindRoute || (options.useFindRoute == undefined && roomDistance > 2))) {
            allowedRooms = this.findRoute(origin.roomName, destination.roomName, options);
        }
        if (options.direct) {
            options.terrainCosts = { plainCost: 1, swampCost: 1 };
        }
        const callback = (roomName) => this.roomCallback(roomName, origin, destination, allowedRooms, options);
        let ret = PathFinder.search(origin, { pos: destination, range: options.range }, {
            maxOps: options.maxOps,
            maxRooms: options.maxRooms,
            plainCost: options.terrainCosts.plainCost,
            swampCost: options.terrainCosts.swampCost,
            roomCallback: callback,
        });
        if (ret.incomplete && options.ensurePath) {
            if (options.useFindRoute == undefined) {
                // handle case where pathfinder failed at a short distance due to not using findRoute
                // can happen for situations where the creep would have to take an uncommonly indirect path
                // options.allowedRooms and options.routeCallback can also be used to handle this situation
                if (roomDistance <= 2) {
                    log.warning(`Movement: path failed without findroute. Origin: ${origin.print}, ` +
                        `destination: ${destination.print}. Trying again with options.useFindRoute = true...`);
                    options.useFindRoute = true;
                    ret = this.findPath(origin, destination, options);
                    log.warning(`Movement: second attempt was ${ret.incomplete ? 'not ' : ''}successful`);
                    return ret;
                }
            }
            else {
            }
        }
        return ret;
    }
    /* Find a path from origin to destination */
    static findSwarmPath(origin, destination, width, height, options = {}) {
        _.defaults(options, {
            ignoreCreeps: true,
            maxOps: 2 * DEFAULT_MAXOPS,
            range: 1,
        });
        // Make copies of the destination offset for where anchor could be
        let destinations = this.getPosWindow(destination, -width, -height);
        const callback = (roomName) => this.swarmRoomCallback(roomName, width, height, options);
        return PathFinder.search(origin, _.map(destinations, pos => ({ pos: pos, range: options.range })), {
            maxOps: options.maxOps,
            maxRooms: options.maxRooms,
            plainCost: 1,
            swampCost: 5,
            roomCallback: callback,
        });
    }
    /* Get a window of offset RoomPositions from an anchor position and a window width and height */
    static getPosWindow(anchor, width, height) {
        let positions = [];
        for (let dx of _.range(0, width, width < 0 ? -1 : 1)) {
            for (let dy of _.range(0, height, height < 0 ? -1 : 1)) {
                positions.push(anchor.getOffsetPos(dx, dy));
            }
        }
        return positions;
    }
    /* Returns the shortest path from start to end position, regardless of (passable) terrain */
    static findShortestPath(startPos, endPos, options = {}) {
        _.defaults(options, {
            ignoreCreeps: true,
            range: 1,
            direct: true,
        });
        let ret = this.findPath(startPos, endPos, options);
        if (ret.incomplete)
            log.alert(`Pathing: incomplete path from ${startPos.print} to ${endPos.print}!`);
        return ret;
    }
    /* Returns the shortest path from start to end position, regardless of (passable) terrain */
    static findPathToRoom(startPos, roomName, options = {}) {
        options.range = 23;
        let ret = this.findPath(startPos, new RoomPosition(25, 25, roomName), options);
        if (ret.incomplete)
            log.alert(`Pathing: incomplete path from ${startPos.print} to ${roomName}!`);
        return ret;
    }
    static roomCallback(roomName, origin, destination, allowedRooms, options) {
        if (allowedRooms && !allowedRooms[roomName]) {
            return false;
        }
        if (!options.allowHostile && this.shouldAvoid(roomName)
            && roomName != origin.roomName && roomName != destination.roomName) {
            return false;
        }
        const room = Game.rooms[roomName];
        if (room) {
            let matrix = this.getCostMatrix(room, options, false);
            // Modify cost matrix if needed
            if (options.modifyRoomCallback) {
                return options.modifyRoomCallback(room, matrix.clone());
            }
            else {
                return matrix;
            }
        }
        else { // have no vision
            return this.getCostMatrixForInvisibleRoom(roomName, options);
        }
    }
    static swarmRoomCallback(roomName, width, height, options) {
        const room = Game.rooms[roomName];
        if (room && !options.ignoreStructures) {
            return this.getSwarmDefaultMatrix(room, width, height, options, false);
        }
        else {
            return this.getSwarmTerrainMatrix(roomName, width, height, options.exitCost);
        }
    }
    static kitingRoomCallback(roomName) {
        const room = Game.rooms[roomName];
        if (room) {
            return Pathing_1.getKitingMatrix(room);
        }
        else { // have no vision
            return true;
        }
    }
    /* Get a kiting path within a room */
    static findKitingPath(creepPos, fleeFrom, options = {}) {
        _.defaults(options, {
            fleeRange: 5,
            terrainCosts: { plainCost: 1, swampCost: 5 },
        });
        let fleeFromPos = _.map(fleeFrom, flee => normalizePos(flee));
        let avoidGoals = _.map(fleeFromPos, pos => {
            return { pos: pos, range: options.fleeRange };
        });
        return PathFinder.search(creepPos, avoidGoals, {
            plainCost: options.terrainCosts.plainCost,
            swampCost: options.terrainCosts.swampCost,
            flee: true,
            roomCallback: Pathing_1.kitingRoomCallback,
            maxRooms: 1
        });
    }
    /* Get a flee path possibly leaving the room; generally called further in advance of kitingPath */
    static findFleePath(creepPos, fleeFrom, options = {}) {
        _.defaults(options, {
            terrainCosts: { plainCost: 1, swampCost: 5 },
        });
        if (options.fleeRange == undefined)
            options.fleeRange = options.terrainCosts.plainCost > 1 ? 20 : 10;
        let fleeFromPos = _.map(fleeFrom, flee => normalizePos(flee));
        let avoidGoals = _.map(fleeFromPos, pos => {
            return { pos: pos, range: options.fleeRange };
        });
        const callback = (roomName) => {
            if (!options.allowHostile && this.shouldAvoid(roomName) && roomName != creepPos.roomName) {
                return false;
            }
            const room = Game.rooms[roomName];
            if (room) {
                let matrix = this.getCostMatrix(room, options, false);
                // Modify cost matrix if needed
                if (options.modifyRoomCallback) {
                    return options.modifyRoomCallback(room, matrix.clone());
                }
                else {
                    return matrix;
                }
            }
            else { // have no vision
                return true;
            }
        };
        return PathFinder.search(creepPos, avoidGoals, {
            plainCost: options.terrainCosts.plainCost,
            swampCost: options.terrainCosts.swampCost,
            flee: true,
            roomCallback: callback,
        });
    }
    // Cost matrix retrieval functions =================================================================================
    /* Get a cloned copy of the cost matrix for a room with specified options */
    static getCostMatrix(room, options, clone = true) {
        let matrix;
        if (options.ignoreCreeps == false) {
            matrix = this.getCreepMatrix(room);
        }
        else if (options.avoidSK) {
            matrix = this.getSkMatrix(room);
        }
        else if (options.ignoreStructures) {
            matrix = new PathFinder.CostMatrix();
        }
        else if (options.direct) {
            matrix = this.getDirectMatrix(room);
        }
        else {
            matrix = this.getDefaultMatrix(room);
        }
        // Register other obstacles
        if (options.obstacles && options.obstacles.length > 0) {
            matrix = matrix.clone();
            for (let obstacle of options.obstacles) {
                if (obstacle && obstacle.roomName == room.name) {
                    matrix.set(obstacle.x, obstacle.y, 0xff);
                }
            }
        }
        if (clone) {
            matrix = matrix.clone();
        }
        return matrix;
    }
    /* Get a cloned copy of the cost matrix for a room with specified options */
    static getSwarmDefaultMatrix(room, width, height, options = {}, clone = true) {
        let matrix = $.costMatrix(room.name, `swarm${width}x${height}`, () => {
            let mat = this.getTerrainMatrix(room.name).clone();
            this.blockImpassibleStructures(mat, room);
            this.setExitCosts(mat, room.name, options.exitCost || 10);
            this.applyMovingMaximum(mat, width, height);
            return mat;
        }, 25);
        if (options.ignoreCreeps == false) {
            matrix = matrix.clone();
            this.blockHostileCreeps(matrix, room); // todo: need to smear again?
        }
        if (clone) {
            matrix = matrix.clone();
        }
        return matrix;
    }
    /* Get a cloned copy of the cost matrix for a room with specified options */
    static getCostMatrixForInvisibleRoom(roomName, options, clone = true) {
        let matrix;
        if (options.avoidSK) {
            matrix = $.costMatrixRecall(roomName, MatrixTypes.sk);
        }
        else if (options.direct) {
            matrix = $.costMatrixRecall(roomName, MatrixTypes.direct);
        }
        else {
            matrix = $.costMatrixRecall(roomName, MatrixTypes.default);
        }
        // Register other obstacles
        if (matrix && options.obstacles && options.obstacles.length > 0) {
            matrix = matrix.clone();
            for (let obstacle of options.obstacles) {
                if (obstacle && obstacle.roomName == roomName) {
                    matrix.set(obstacle.x, obstacle.y, 0xff);
                }
            }
        }
        if (matrix && clone) {
            matrix = matrix.clone();
        }
        return matrix || true;
    }
    // Cost matrix generation functions ================================================================================
    /* Get a matrix of explicit terrain values for a room */
    static getTerrainMatrix(roomName, costs = { plainCost: 1, swampCost: 5 }) {
        return $.costMatrix(roomName, `terrain:${costs.plainCost}:${costs.swampCost}`, () => {
            let matrix = new PathFinder.CostMatrix();
            const terrain = Game.map.getRoomTerrain(roomName);
            for (let y = 0; y < 50; ++y) {
                for (let x = 0; x < 50; ++x) {
                    switch (terrain.get(x, y)) {
                        case TERRAIN_MASK_SWAMP:
                            matrix.set(x, y, costs.swampCost);
                            break;
                        case TERRAIN_MASK_WALL:
                            matrix.set(x, y, 0xff);
                            break;
                        default: // plain
                            matrix.set(x, y, costs.plainCost);
                            break;
                    }
                }
            }
            return matrix;
        }, 10000);
    }
    /* Get a cloned copy of the cost matrix for a room with specified options */
    static getSwarmTerrainMatrix(roomName, width, height, exitCost = 10) {
        let matrix = $.costMatrix(roomName, `swarmTerrain${width}x${height}EC${exitCost}`, () => {
            let mat = this.getTerrainMatrix(roomName).clone();
            this.setExitCosts(mat, roomName, exitCost);
            this.applyMovingMaximum(mat, width, height);
            return mat;
        }, 10000);
        return matrix;
    }
    /* Default matrix for a room, setting impassable structures and constructionSites to impassible */
    static getDefaultMatrix(room) {
        return $.costMatrix(room.name, MatrixTypes.default, () => {
            let matrix = new PathFinder.CostMatrix();
            // Set passability of structure positions
            let impassibleStructures = [];
            _.forEach(room.find(FIND_STRUCTURES), (s) => {
                if (s.structureType == STRUCTURE_ROAD) {
                    matrix.set(s.pos.x, s.pos.y, 1);
                }
                else if (!s.isWalkable) {
                    impassibleStructures.push(s);
                }
            });
            _.forEach(impassibleStructures, s => matrix.set(s.pos.x, s.pos.y, 0xff));
            // Set passability of construction sites
            _.forEach(room.find(FIND_CONSTRUCTION_SITES), (site) => {
                if (site.my && !site.isWalkable) {
                    matrix.set(site.pos.x, site.pos.y, 0xff);
                }
            });
            return matrix;
        });
    }
    /* Default matrix for a room, setting impassable structures and constructionSites to impassible, ignoring roads */
    static getDirectMatrix(room) {
        return $.costMatrix(room.name, MatrixTypes.direct, () => {
            let matrix = new PathFinder.CostMatrix();
            // Set passability of structure positions
            let impassibleStructures = [];
            _.forEach(room.find(FIND_STRUCTURES), (s) => {
                if (!s.isWalkable) {
                    impassibleStructures.push(s);
                }
            });
            _.forEach(impassibleStructures, s => matrix.set(s.pos.x, s.pos.y, 0xff));
            // Set passability of construction sites
            _.forEach(room.find(FIND_MY_CONSTRUCTION_SITES), (site) => {
                if (!site.isWalkable) {
                    matrix.set(site.pos.x, site.pos.y, 0xff);
                }
            });
            return matrix;
        });
    }
    /* Avoids creeps in a room */
    static getCreepMatrix(room, fromMatrix) {
        if (room._creepMatrix) {
            return room._creepMatrix;
        }
        let matrix = this.getDefaultMatrix(room).clone();
        _.forEach(room.find(FIND_CREEPS), c => matrix.set(c.pos.x, c.pos.y, CREEP_COST)); // don't block off entirely
        room._creepMatrix = matrix;
        return room._creepMatrix;
    }
    /* Kites around hostile creeps in a room */
    static getKitingMatrix(room) {
        if (room._kitingMatrix) {
            return room._kitingMatrix;
        }
        let matrix = this.getCreepMatrix(room).clone();
        let avoidCreeps = _.filter(room.hostiles, c => c.getActiveBodyparts(ATTACK) > 0 || c.getActiveBodyparts(RANGED_ATTACK) > 0); // || c.getActiveBodyparts(HEAL) > 0);
        _.forEach(avoidCreeps, avoidCreep => {
            let cost;
            for (let dx = -3; dx <= 3; dx++) {
                for (let dy = -3; dy <= 3; dy++) {
                    cost = matrix.get(avoidCreep.pos.x + dx, avoidCreep.pos.y + dy);
                    cost += 40 - (10 * Math.max(Math.abs(dx), Math.abs(dy)));
                    matrix.set(avoidCreep.pos.x + dx, avoidCreep.pos.y + dy, cost);
                }
            }
        });
        room._kitingMatrix = matrix;
        return room._kitingMatrix;
    }
    /* Avoids source keepers in a room */
    static getSkMatrix(room) {
        if (Cartographer.roomType(room.name) != ROOMTYPE_SOURCEKEEPER) {
            return this.getDefaultMatrix(room);
        }
        return $.costMatrix(room.name, MatrixTypes.sk, () => {
            let matrix = this.getDefaultMatrix(room).clone();
            const avoidRange = 6;
            _.forEach(room.keeperLairs, lair => {
                for (let dx = -avoidRange; dx <= avoidRange; dx++) {
                    for (let dy = -avoidRange; dy <= avoidRange; dy++) {
                        matrix.set(lair.pos.x + dx, lair.pos.y + dy, 0xfe);
                    }
                }
            });
            return matrix;
        });
    }
    // /* Avoids source keepers in a room */
    // private static getInvisibleSkMatrix(roomName: string): CostMatrix {
    // 	let matrix = new PathFinder.CostMatrix();
    // 	if (Cartographer.roomType(roomName) == ROOMTYPE_SOURCEKEEPER) {
    // 		if (Memory.rooms[roomName] && Memory.rooms[roomName].SKlairs != undefined) {
    //
    // 			const avoidRange = 5;
    // 			const lairs: RoomPosition[] = _.map(Memory.rooms[roomName].SKlairs!,
    // 												saved => derefCoords(saved.c, roomName));
    // 			_.forEach(lairs, lair => {
    // 				for (let dx = -avoidRange; dx <= avoidRange; dx++) {
    // 					for (let dy = -avoidRange; dy <= avoidRange; dy++) {
    // 						matrix.set(lair.x + dx, lair.y + dy, 0xff);
    // 					}
    // 				}
    // 			});
    // 		}
    // 	}
    // 	return matrix;
    // }
    // In-place CostMatrix manipulation routines =======================================================================
    /* Sets impassible structure positions to 0xff */
    static blockImpassibleStructures(matrix, room) {
        _.forEach(room.find(FIND_STRUCTURES), (s) => {
            if (!s.isWalkable) {
                matrix.set(s.pos.x, s.pos.y, 0xff);
            }
        });
    }
    /* Sets hostile creep positions to impassible */
    static blockHostileCreeps(matrix, room) {
        _.forEach(room.hostiles, hostile => {
            matrix.set(hostile.pos.x, hostile.pos.y, CREEP_COST);
        });
    }
    /* Sets all creep positions to impassible */
    static blockAllCreeps(matrix, room) {
        _.forEach(room.find(FIND_CREEPS), hostile => {
            matrix.set(hostile.pos.x, hostile.pos.y, CREEP_COST);
        });
    }
    /* Sets road positions to 1 if cost is less than 0xfe */
    static preferRoads(matrix, room) {
        _.forEach(room.roads, road => {
            if (matrix.get(road.pos.x, road.pos.y) < 0xfe) {
                matrix.set(road.pos.x, road.pos.y, 1);
            }
        });
    }
    /* Sets walkable rampart positions to 1 if cost is less than 0xfe */
    static preferRamparts(matrix, room) {
        _.forEach(room.walkableRamparts, rampart => {
            if (matrix.get(rampart.pos.x, rampart.pos.y) < 0xfe) {
                matrix.set(rampart.pos.x, rampart.pos.y, 1);
            }
        });
    }
    /* Explicitly blocks off walls for a room */
    static blockImpassibleTerrain(matrix, roomName) {
        const terrain = Game.map.getRoomTerrain(roomName);
        for (let y = 0; y < 50; ++y) {
            for (let x = 0; x < 50; ++x) {
                if (terrain.get(x, y) === TERRAIN_MASK_WALL) {
                    matrix.set(x, y, 0xff);
                }
            }
        }
    }
    /* Transform a CostMatrix such that the cost at each point is transformed to the max of costs in a width x height
     * window (indexed from upper left corner). This requires that terrain be explicitly specified in the matrix! */
    static applyMovingMaximum(matrix, width, height) {
        // Since we're moving in increasing order of x, y, we don't need to clone the matrix
        var x, y, dx, dy;
        var maxCost, cost;
        for (x = 0; x < 50 - width; x++) {
            for (y = 0; y < 50 - height; y++) {
                maxCost = matrix.get(x, y);
                for (dx = 0; dx <= width - 1; dx++) {
                    for (dy = 0; dy <= height - 1; dy++) {
                        cost = matrix.get(x + dx, y + dy);
                        if (cost > maxCost) {
                            maxCost = cost;
                        }
                    }
                }
                matrix.set(x, y, maxCost);
            }
        }
    }
    static setCostsInRange(matrix, pos, range, cost = 30, add = false) {
        pos = normalizePos(pos);
        const terrain = Game.map.getRoomTerrain(pos.roomName);
        for (let dx = -range; dx <= range; dx++) {
            let x = pos.x + dx;
            if (x < 0 || x > 49)
                continue;
            for (let dy = -range; dy <= range; dy++) {
                let y = pos.y + dy;
                if (y < 0 || y > 49)
                    continue;
                let posTerrain = terrain.get(x, y);
                if (posTerrain === TERRAIN_MASK_WALL) {
                    continue;
                }
                let currentCost = matrix.get(x, y);
                if (currentCost === 0) {
                    if (posTerrain === TERRAIN_MASK_SWAMP) {
                        currentCost += 10;
                    }
                    else {
                        currentCost += 2;
                    }
                }
                if (currentCost >= 0xff || currentCost > cost)
                    continue;
                matrix.set(x, y, add ? Math.min(cost + currentCost, 200) : cost);
            }
        }
    }
    static blockExits(matrix, rangeToEdge = 0) {
        for (let x = rangeToEdge; x < 50 - rangeToEdge; x += 49 - rangeToEdge * 2) {
            for (let y = rangeToEdge; y < 50 - rangeToEdge; y++) {
                matrix.set(x, y, 0xff);
            }
        }
        for (let x = rangeToEdge; x < 50 - rangeToEdge; x++) {
            for (let y = rangeToEdge; y < 50 - rangeToEdge; y += 49 - rangeToEdge * 2) {
                matrix.set(x, y, 0xff);
            }
        }
    }
    static setExitCosts(matrix, roomName, cost, rangeToEdge = 0) {
        const terrain = Game.map.getRoomTerrain(roomName);
        for (let x = rangeToEdge; x < 50 - rangeToEdge; x += 49 - rangeToEdge * 2) {
            for (let y = rangeToEdge; y < 50 - rangeToEdge; y++) {
                if (terrain.get(x, y) != TERRAIN_MASK_WALL) {
                    matrix.set(x, y, cost);
                }
            }
        }
        for (let x = rangeToEdge; x < 50 - rangeToEdge; x++) {
            for (let y = rangeToEdge; y < 50 - rangeToEdge; y += 49 - rangeToEdge * 2) {
                if (terrain.get(x, y) != TERRAIN_MASK_WALL) {
                    matrix.set(x, y, cost);
                }
            }
        }
    }
    /* Find a viable sequence of rooms to narrow down Pathfinder algorithm */
    static findRoute(origin, destination, options = {}) {
        let linearDistance = Game.map.getRoomLinearDistance(origin, destination);
        let restrictDistance = options.restrictDistance || linearDistance + 10;
        let allowedRooms = { [origin]: true, [destination]: true };
        // Determine whether to use highway bias
        let highwayBias = 1;
        if (options.preferHighway) {
            highwayBias = 2.5;
        }
        else if (options.preferHighway != false) {
            // if (linearDistance > 8) {
            // 	highwayBias = 2.5;
            // } else {
            // 	let oCoords = Cartographer.getRoomCoordinates(origin);
            // 	let dCoords = Cartographer.getRoomCoordinates(destination);
            // 	if (_.any([oCoords.x, oCoords.y, dCoords.x, dCoords.y], z => z % 10 <= 1 || z % 10 >= 9)) {
            // 		highwayBias = 2.5;
            // 	}
            // }
        }
        let ret = Game.map.findRoute(origin, destination, {
            routeCallback: (roomName) => {
                let rangeToRoom = Game.map.getRoomLinearDistance(origin, roomName);
                if (rangeToRoom > restrictDistance) { // room is too far out of the way
                    return Number.POSITIVE_INFINITY;
                }
                if (!options.allowHostile && this.shouldAvoid(roomName) &&
                    roomName !== destination && roomName !== origin) { // room is marked as "avoid" in room memory
                    return Number.POSITIVE_INFINITY;
                }
                if (options.preferHighway && Cartographer.roomType(roomName) == ROOMTYPE_ALLEY) {
                    return 1;
                }
                return highwayBias;
            },
        });
        if (!_.isArray(ret)) {
            log.warning(`Movement: couldn't findRoute from ${origin} to ${destination}!`);
        }
        else {
            for (let value of ret) {
                allowedRooms[value.room] = true;
            }
            return allowedRooms;
        }
    }
    /* Serialize a path as a string of move directions */
    static serializePath(startPos, path, color = 'orange') {
        let serializedPath = '';
        let lastPosition = startPos;
        for (let position of path) {
            if (position.roomName == lastPosition.roomName) {
                new RoomVisual(position.roomName)
                    .line(position, lastPosition, { color: color, lineStyle: 'dashed' });
                serializedPath += lastPosition.getDirectionTo(position);
            }
            lastPosition = position;
        }
        return serializedPath;
    }
    static nextDirectionInPath(creep) {
        let moveData = creep.memory._go;
        if (!moveData || !moveData.path || moveData.path.length == 0) {
            return;
        }
        return Number.parseInt(moveData.path[0]);
    }
    static nextPositionInPath(creep) {
        let nextDir = this.nextDirectionInPath(creep);
        if (!nextDir) {
            return;
        }
        return this.positionAtDirection(creep.pos, nextDir);
    }
    static oppositeDirection(direction) {
        switch (direction) {
            case TOP:
                return BOTTOM;
            case TOP_LEFT:
                return BOTTOM_RIGHT;
            case LEFT:
                return RIGHT;
            case BOTTOM_LEFT:
                return TOP_RIGHT;
            case BOTTOM:
                return TOP;
            case BOTTOM_RIGHT:
                return TOP_LEFT;
            case RIGHT:
                return LEFT;
            case TOP_RIGHT:
                return BOTTOM_LEFT;
        }
    }
    /* Returns a position at a direction from origin */
    static positionAtDirection(origin, direction) {
        const offsetX = [0, 0, 1, 1, 1, 0, -1, -1, -1];
        const offsetY = [0, -1, -1, 0, 1, 1, 1, 0, -1];
        let x = origin.x + offsetX[direction];
        let y = origin.y + offsetY[direction];
        if (x > 49 || x < 0 || y > 49 || y < 0) {
            return;
        }
        return new RoomPosition(x, y, origin.roomName);
    }
    static savePath(path) {
        let savedPath = {
            path: path,
            length: path.length,
            tick: Game.time
        };
        let originName = _.first(path).name;
        let destinationName = _.last(path).name;
        if (!Memory.pathing.paths[originName]) {
            Memory.pathing.paths[originName] = {};
        }
        Memory.pathing.paths[originName][destinationName] = savedPath;
    }
    // Distance and path weight calculations ===========================================================================
    /* Calculate and/or cache the length of the shortest path between two points.
     * Cache is probabilistically cleared in Mem */
    static distance(arg1, arg2) {
        let [name1, name2] = [arg1.name, arg2.name].sort(); // alphabetize since path is the same in either direction
        if (!Memory.pathing.distances[name1]) {
            Memory.pathing.distances[name1] = {};
        }
        if (!Memory.pathing.distances[name1][name2]) {
            let ret = this.findShortestPath(arg1, arg2);
            if (!ret.incomplete) {
                Memory.pathing.distances[name1][name2] = ret.path.length;
            }
        }
        return Memory.pathing.distances[name1][name2];
    }
    static calculatePathWeight(startPos, endPos, options = {}) {
        _.defaults(options, {
            range: 1,
        });
        let ret = this.findPath(startPos, endPos, options);
        let weight = 0;
        for (let pos of ret.path) {
            if (!pos.room) { // If you don't have vision, assume there are roads
                weight += 1;
            }
            else {
                if (pos.lookForStructure(STRUCTURE_ROAD)) {
                    weight += 1;
                }
                else {
                    let terrain = pos.lookFor(LOOK_TERRAIN)[0];
                    if (terrain == 'plain') {
                        weight += 2;
                    }
                    else if (terrain == 'swamp') {
                        weight += 10;
                    }
                }
            }
        }
        return weight;
    }
    /* Calculates and/or caches the weighted distance for the most efficient path. Weight is sum of tile weights:
     * Road = 1, Plain = 2, Swamp = 10. Cached weights are cleared in Mem occasionally. */
    static weightedDistance(arg1, arg2) {
        let pos1, pos2;
        if (arg1.name < arg2.name) { // alphabetize since path lengths are the same either direction
            pos1 = arg1;
            pos2 = arg2;
        }
        else {
            pos1 = arg2;
            pos2 = arg1;
        }
        if (!Memory.pathing.weightedDistances[pos1.name]) {
            Memory.pathing.weightedDistances[pos1.name] = {};
        }
        if (!Memory.pathing.weightedDistances[pos1.name][pos2.name]) {
            Memory.pathing.weightedDistances[pos1.name][pos2.name] = this.calculatePathWeight(pos1, pos2);
        }
        return Memory.pathing.weightedDistances[pos1.name][pos2.name];
    }
    /* Whether another object in the same room can be reached from the current position */
    static isReachable(startPos, endPos, obstacles, options = {}) {
        _.defaults(options, {
            ignoreCreeps: true,
            range: 1,
            maxOps: 2000,
            ensurePath: false,
        });
        if (startPos.roomName != endPos.roomName) {
            log.error(`isReachable() should only be used within a single room!`);
            return false;
        }
        let matrix = new PathFinder.CostMatrix();
        _.forEach(obstacles, obstacle => {
            if (hasPos(obstacle)) {
                matrix.set(obstacle.pos.x, obstacle.pos.y, 0xfe);
            }
            else {
                matrix.set(obstacle.x, obstacle.y, 0xfe);
            }
        });
        let callback = (roomName) => roomName == endPos.roomName ? matrix : false;
        let ret = PathFinder.search(startPos, { pos: endPos, range: options.range }, {
            maxOps: options.maxOps,
            plainCost: 1,
            swampCost: 5,
            maxRooms: 1,
            roomCallback: callback,
        });
        if (ret.incomplete) {
            return false;
        }
        else {
            for (let pos of ret.path) {
                if (matrix.get(pos.x, pos.y) > 100) {
                    return false;
                }
            }
        }
        return true;
    }
    /* Like isReachable(), but returns the first position which should be cleared to find a path to destination */
    static findBlockingPos(startPos, endPos, obstacles, options = {}) {
        _.defaults(options, {
            ignoreCreeps: true,
            range: 1,
            maxOps: 2000,
            ensurePath: false,
        });
        if (startPos.roomName != endPos.roomName) {
            log.error(`findBlockingPos() should only be used within a single room!`);
            return undefined;
        }
        let matrix = new PathFinder.CostMatrix();
        _.forEach(obstacles, obstacle => {
            if (hasPos(obstacle)) {
                matrix.set(obstacle.pos.x, obstacle.pos.y, 0xfe);
            }
            else {
                matrix.set(obstacle.x, obstacle.y, 0xfe);
            }
        });
        let callback = (roomName) => roomName == endPos.roomName ? matrix : false;
        let ret = PathFinder.search(startPos, { pos: endPos, range: options.range }, {
            maxOps: options.maxOps,
            plainCost: 1,
            swampCost: 5,
            maxRooms: 1,
            roomCallback: callback,
        });
        for (let pos of ret.path) {
            if (matrix.get(pos.x, pos.y) > 100) {
                return pos;
            }
        }
    }
    /* Find the first walkable position in the room, spiraling outward from the center */
    static findPathablePosition(roomName, clearance = { width: 1, height: 1 }) {
        const terrain = Game.map.getRoomTerrain(roomName);
        let x, y;
        let allClear;
        for (let radius = 0; radius < 23; radius++) {
            for (let dx = -radius; dx <= radius; dx++) {
                for (let dy = -radius; dy <= radius; dy++) {
                    if (Math.abs(dy) !== radius && Math.abs(dx) !== radius) {
                        continue;
                    }
                    x = 25 + dx;
                    y = 25 + dy;
                    allClear = true;
                    for (let w = 0; w < clearance.width; w++) {
                        for (let h = 0; h < clearance.height; h++) {
                            if (terrain.get(x + w, y + h) === TERRAIN_MASK_WALL) {
                                allClear = false;
                            }
                        }
                    }
                    if (allClear) {
                        return new RoomPosition(x, y, roomName);
                    }
                }
            }
        }
        // Should never reach here!
        return new RoomPosition(-10, -10, 'cannotFindPathablePosition');
    }
};
Pathing = Pathing_1 = __decorate([
    profile
], Pathing);

// @formatter:off
var hatcheryLayout = { data: { anchor: { 'x': 25, 'y': 24 }, }, 1: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '1', 'buildings': { 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }] } } }, 2: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '2', 'buildings': { 'extension': { 'pos': [{ 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 27, 'y': 26 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] } } }, 3: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '3', 'buildings': { 'extension': { 'pos': [{ 'x': 24, 'y': 22 }, { 'x': 26, 'y': 22 }, { 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 23, 'y': 26 }, { 'x': 27, 'y': 26 }, { 'x': 24, 'y': 27 }, { 'x': 26, 'y': 27 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] } } }, 4: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '4', 'buildings': { 'road': { 'pos': [{ 'x': 25, 'y': 25 }, { 'x': 25, 'y': 20 }, { 'x': 21, 'y': 21 }, { 'x': 24, 'y': 21 }, { 'x': 26, 'y': 21 }, { 'x': 29, 'y': 21 }, { 'x': 22, 'y': 22 }, { 'x': 25, 'y': 22 }, { 'x': 28, 'y': 22 }, { 'x': 23, 'y': 23 }, { 'x': 25, 'y': 23 }, { 'x': 27, 'y': 23 }, { 'x': 21, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 29, 'y': 24 }, { 'x': 20, 'y': 25 }, { 'x': 22, 'y': 25 }, { 'x': 23, 'y': 25 }, { 'x': 27, 'y': 25 }, { 'x': 28, 'y': 25 }, { 'x': 30, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 29, 'y': 26 }, { 'x': 23, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 27, 'y': 27 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 28, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 29, 'y': 29 }, { 'x': 25, 'y': 30 }] }, 'extension': { 'pos': [{ 'x': 23, 'y': 22 }, { 'x': 24, 'y': 22 }, { 'x': 26, 'y': 22 }, { 'x': 27, 'y': 22 }, { 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 28, 'y': 24 }, { 'x': 22, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 27, 'y': 26 }, { 'x': 28, 'y': 26 }, { 'x': 24, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 27, 'y': 28 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] } } }, 5: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '5', 'buildings': { 'road': { 'pos': [{ 'x': 25, 'y': 25 }, { 'x': 25, 'y': 20 }, { 'x': 21, 'y': 21 }, { 'x': 24, 'y': 21 }, { 'x': 26, 'y': 21 }, { 'x': 29, 'y': 21 }, { 'x': 22, 'y': 22 }, { 'x': 25, 'y': 22 }, { 'x': 28, 'y': 22 }, { 'x': 23, 'y': 23 }, { 'x': 25, 'y': 23 }, { 'x': 27, 'y': 23 }, { 'x': 21, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 29, 'y': 24 }, { 'x': 20, 'y': 25 }, { 'x': 22, 'y': 25 }, { 'x': 23, 'y': 25 }, { 'x': 27, 'y': 25 }, { 'x': 28, 'y': 25 }, { 'x': 30, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 29, 'y': 26 }, { 'x': 23, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 27, 'y': 27 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 28, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 29, 'y': 29 }, { 'x': 25, 'y': 30 }] }, 'extension': { 'pos': [{ 'x': 23, 'y': 21 }, { 'x': 27, 'y': 21 }, { 'x': 23, 'y': 22 }, { 'x': 24, 'y': 22 }, { 'x': 26, 'y': 22 }, { 'x': 27, 'y': 22 }, { 'x': 21, 'y': 23 }, { 'x': 22, 'y': 23 }, { 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 28, 'y': 23 }, { 'x': 29, 'y': 23 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 28, 'y': 24 }, { 'x': 22, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 27, 'y': 26 }, { 'x': 28, 'y': 26 }, { 'x': 22, 'y': 27 }, { 'x': 24, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 28, 'y': 27 }, { 'x': 29, 'y': 27 }, { 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 27, 'y': 28 }, { 'x': 27, 'y': 29 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'tower': { 'pos': [{ 'x': 29, 'y': 25 }] }, 'link': { 'pos': [{ 'x': 25, 'y': 26 }] } } }, 6: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '6', 'buildings': { 'road': { 'pos': [{ 'x': 25, 'y': 25 }, { 'x': 25, 'y': 20 }, { 'x': 21, 'y': 21 }, { 'x': 24, 'y': 21 }, { 'x': 26, 'y': 21 }, { 'x': 29, 'y': 21 }, { 'x': 22, 'y': 22 }, { 'x': 25, 'y': 22 }, { 'x': 28, 'y': 22 }, { 'x': 23, 'y': 23 }, { 'x': 25, 'y': 23 }, { 'x': 27, 'y': 23 }, { 'x': 21, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 29, 'y': 24 }, { 'x': 20, 'y': 25 }, { 'x': 22, 'y': 25 }, { 'x': 23, 'y': 25 }, { 'x': 27, 'y': 25 }, { 'x': 28, 'y': 25 }, { 'x': 30, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 29, 'y': 26 }, { 'x': 23, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 27, 'y': 27 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 28, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 29, 'y': 29 }, { 'x': 25, 'y': 30 }] }, 'extension': { 'pos': [{ 'x': 22, 'y': 21 }, { 'x': 23, 'y': 21 }, { 'x': 27, 'y': 21 }, { 'x': 28, 'y': 21 }, { 'x': 21, 'y': 22 }, { 'x': 23, 'y': 22 }, { 'x': 24, 'y': 22 }, { 'x': 26, 'y': 22 }, { 'x': 27, 'y': 22 }, { 'x': 29, 'y': 22 }, { 'x': 21, 'y': 23 }, { 'x': 22, 'y': 23 }, { 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 28, 'y': 23 }, { 'x': 29, 'y': 23 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 28, 'y': 24 }, { 'x': 22, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 27, 'y': 26 }, { 'x': 28, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 24, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 28, 'y': 27 }, { 'x': 29, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 27, 'y': 28 }, { 'x': 29, 'y': 28 }, { 'x': 22, 'y': 29 }, { 'x': 23, 'y': 29 }, { 'x': 27, 'y': 29 }, { 'x': 28, 'y': 29 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'tower': { 'pos': [{ 'x': 29, 'y': 25 }] }, 'link': { 'pos': [{ 'x': 25, 'y': 26 }] } } }, 7: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '7', 'buildings': { 'extension': { 'pos': [{ 'x': 21, 'y': 20 }, { 'x': 22, 'y': 20 }, { 'x': 28, 'y': 20 }, { 'x': 29, 'y': 20 }, { 'x': 20, 'y': 21 }, { 'x': 22, 'y': 21 }, { 'x': 23, 'y': 21 }, { 'x': 27, 'y': 21 }, { 'x': 28, 'y': 21 }, { 'x': 30, 'y': 21 }, { 'x': 20, 'y': 22 }, { 'x': 21, 'y': 22 }, { 'x': 23, 'y': 22 }, { 'x': 24, 'y': 22 }, { 'x': 26, 'y': 22 }, { 'x': 27, 'y': 22 }, { 'x': 29, 'y': 22 }, { 'x': 30, 'y': 22 }, { 'x': 21, 'y': 23 }, { 'x': 22, 'y': 23 }, { 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 28, 'y': 23 }, { 'x': 29, 'y': 23 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 28, 'y': 24 }, { 'x': 22, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 27, 'y': 26 }, { 'x': 28, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 24, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 28, 'y': 27 }, { 'x': 29, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 27, 'y': 28 }, { 'x': 29, 'y': 28 }, { 'x': 20, 'y': 29 }, { 'x': 22, 'y': 29 }, { 'x': 23, 'y': 29 }, { 'x': 27, 'y': 29 }, { 'x': 28, 'y': 29 }, { 'x': 30, 'y': 29 }] }, 'road': { 'pos': [{ 'x': 25, 'y': 25 }, { 'x': 25, 'y': 20 }, { 'x': 21, 'y': 21 }, { 'x': 24, 'y': 21 }, { 'x': 26, 'y': 21 }, { 'x': 29, 'y': 21 }, { 'x': 22, 'y': 22 }, { 'x': 25, 'y': 22 }, { 'x': 28, 'y': 22 }, { 'x': 23, 'y': 23 }, { 'x': 25, 'y': 23 }, { 'x': 27, 'y': 23 }, { 'x': 21, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 29, 'y': 24 }, { 'x': 20, 'y': 25 }, { 'x': 22, 'y': 25 }, { 'x': 23, 'y': 25 }, { 'x': 27, 'y': 25 }, { 'x': 28, 'y': 25 }, { 'x': 30, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 29, 'y': 26 }, { 'x': 23, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 27, 'y': 27 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 28, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 29, 'y': 29 }, { 'x': 25, 'y': 30 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }, { 'x': 24, 'y': 25 }] }, 'tower': { 'pos': [{ 'x': 29, 'y': 25 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'link': { 'pos': [{ 'x': 25, 'y': 26 }] } } }, 8: { 'name': 'hatchery', 'shard': 'shard0', 'rcl': '8', 'buildings': { 'extension': { 'pos': [{ 'x': 20, 'y': 20 }, { 'x': 21, 'y': 20 }, { 'x': 22, 'y': 20 }, { 'x': 28, 'y': 20 }, { 'x': 29, 'y': 20 }, { 'x': 30, 'y': 20 }, { 'x': 20, 'y': 21 }, { 'x': 22, 'y': 21 }, { 'x': 23, 'y': 21 }, { 'x': 27, 'y': 21 }, { 'x': 28, 'y': 21 }, { 'x': 30, 'y': 21 }, { 'x': 20, 'y': 22 }, { 'x': 21, 'y': 22 }, { 'x': 23, 'y': 22 }, { 'x': 24, 'y': 22 }, { 'x': 26, 'y': 22 }, { 'x': 27, 'y': 22 }, { 'x': 29, 'y': 22 }, { 'x': 30, 'y': 22 }, { 'x': 21, 'y': 23 }, { 'x': 22, 'y': 23 }, { 'x': 24, 'y': 23 }, { 'x': 26, 'y': 23 }, { 'x': 28, 'y': 23 }, { 'x': 29, 'y': 23 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 27, 'y': 24 }, { 'x': 28, 'y': 24 }, { 'x': 22, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 27, 'y': 26 }, { 'x': 28, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 24, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 28, 'y': 27 }, { 'x': 29, 'y': 27 }, { 'x': 20, 'y': 28 }, { 'x': 21, 'y': 28 }, { 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 27, 'y': 28 }, { 'x': 29, 'y': 28 }, { 'x': 30, 'y': 28 }, { 'x': 20, 'y': 29 }, { 'x': 22, 'y': 29 }, { 'x': 23, 'y': 29 }, { 'x': 27, 'y': 29 }, { 'x': 28, 'y': 29 }, { 'x': 30, 'y': 29 }, { 'x': 20, 'y': 30 }, { 'x': 21, 'y': 30 }, { 'x': 22, 'y': 30 }, { 'x': 28, 'y': 30 }, { 'x': 29, 'y': 30 }, { 'x': 30, 'y': 30 }] }, 'road': { 'pos': [{ 'x': 25, 'y': 25 }, { 'x': 25, 'y': 20 }, { 'x': 21, 'y': 21 }, { 'x': 24, 'y': 21 }, { 'x': 26, 'y': 21 }, { 'x': 29, 'y': 21 }, { 'x': 22, 'y': 22 }, { 'x': 25, 'y': 22 }, { 'x': 28, 'y': 22 }, { 'x': 23, 'y': 23 }, { 'x': 25, 'y': 23 }, { 'x': 27, 'y': 23 }, { 'x': 21, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 29, 'y': 24 }, { 'x': 20, 'y': 25 }, { 'x': 22, 'y': 25 }, { 'x': 23, 'y': 25 }, { 'x': 27, 'y': 25 }, { 'x': 28, 'y': 25 }, { 'x': 30, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 29, 'y': 26 }, { 'x': 23, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 27, 'y': 27 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 28, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 29, 'y': 29 }, { 'x': 25, 'y': 30 }] }, 'tower': { 'pos': [{ 'x': 25, 'y': 21 }, { 'x': 21, 'y': 25 }, { 'x': 29, 'y': 25 }, { 'x': 25, 'y': 29 }] }, 'spawn': { 'pos': [{ 'x': 25, 'y': 24 }, { 'x': 24, 'y': 25 }, { 'x': 26, 'y': 25 }] }, 'container': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'link': { 'pos': [{ 'x': 25, 'y': 26 }] } } }, };

// @formatter:off
var commandCenterLayout = { data: { anchor: { 'x': 25, 'y': 25 } }, 3: { 'name': 'commandCenter', 'shard': 'shard0', 'rcl': '3', 'buildings': { 'tower': { 'pos': [{ 'x': 24, 'y': 27 }] } } }, 4: { 'name': 'commandCenter', 'shard': 'shard0', 'rcl': '4', 'buildings': { 'road': { 'pos': [{ 'x': 21, 'y': 24 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 25, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 21, 'y': 25 }, { 'x': 26, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 21, 'y': 30 }, { 'x': 26, 'y': 30 }, { 'x': 21, 'y': 31 }, { 'x': 22, 'y': 31 }, { 'x': 23, 'y': 31 }, { 'x': 24, 'y': 31 }, { 'x': 25, 'y': 31 }, { 'x': 26, 'y': 31 }] }, 'storage': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'tower': { 'pos': [{ 'x': 24, 'y': 27 }] } } }, 5: { 'name': 'commandCenter', 'shard': 'shard0', 'rcl': '5', 'buildings': { 'road': { 'pos': [{ 'x': 21, 'y': 24 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 25, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 21, 'y': 25 }, { 'x': 26, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 21, 'y': 30 }, { 'x': 26, 'y': 30 }, { 'x': 21, 'y': 31 }, { 'x': 22, 'y': 31 }, { 'x': 23, 'y': 31 }, { 'x': 24, 'y': 31 }, { 'x': 25, 'y': 31 }, { 'x': 26, 'y': 31 }] }, 'link': { 'pos': [{ 'x': 24, 'y': 25 }] }, 'storage': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'tower': { 'pos': [{ 'x': 24, 'y': 27 }] } } }, 6: { 'name': 'commandCenter', 'shard': 'shard0', 'rcl': '6', 'buildings': { 'road': { 'pos': [{ 'x': 21, 'y': 24 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 25, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 21, 'y': 25 }, { 'x': 26, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 21, 'y': 30 }, { 'x': 26, 'y': 30 }, { 'x': 21, 'y': 31 }, { 'x': 22, 'y': 31 }, { 'x': 23, 'y': 31 }, { 'x': 24, 'y': 31 }, { 'x': 25, 'y': 31 }, { 'x': 26, 'y': 31 }] }, 'link': { 'pos': [{ 'x': 24, 'y': 25 }] }, 'storage': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'terminal': { 'pos': [{ 'x': 25, 'y': 26 }] }, 'tower': { 'pos': [{ 'x': 24, 'y': 27 }] }, 'lab': { 'pos': [{ 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 24, 'y': 29 }] } } }, 7: { 'name': 'commandCenter', 'shard': 'shard0', 'rcl': '7', 'buildings': { 'road': { 'pos': [{ 'x': 21, 'y': 24 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 25, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 21, 'y': 25 }, { 'x': 26, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 21, 'y': 30 }, { 'x': 26, 'y': 30 }, { 'x': 21, 'y': 31 }, { 'x': 22, 'y': 31 }, { 'x': 23, 'y': 31 }, { 'x': 24, 'y': 31 }, { 'x': 25, 'y': 31 }, { 'x': 26, 'y': 31 }] }, 'link': { 'pos': [{ 'x': 24, 'y': 25 }] }, 'storage': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'terminal': { 'pos': [{ 'x': 25, 'y': 26 }] }, 'tower': { 'pos': [{ 'x': 23, 'y': 27 }, { 'x': 24, 'y': 27 }] }, 'lab': { 'pos': [{ 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 22, 'y': 29 }, { 'x': 23, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 25, 'y': 29 }] } } }, 8: { 'name': 'commandCenter', 'shard': 'shard0', 'rcl': '8', 'buildings': { 'road': { 'pos': [{ 'x': 21, 'y': 24 }, { 'x': 22, 'y': 24 }, { 'x': 23, 'y': 24 }, { 'x': 24, 'y': 24 }, { 'x': 25, 'y': 24 }, { 'x': 26, 'y': 24 }, { 'x': 21, 'y': 25 }, { 'x': 26, 'y': 25 }, { 'x': 21, 'y': 26 }, { 'x': 23, 'y': 26 }, { 'x': 24, 'y': 26 }, { 'x': 26, 'y': 26 }, { 'x': 21, 'y': 27 }, { 'x': 22, 'y': 27 }, { 'x': 25, 'y': 27 }, { 'x': 26, 'y': 27 }, { 'x': 21, 'y': 28 }, { 'x': 22, 'y': 28 }, { 'x': 25, 'y': 28 }, { 'x': 26, 'y': 28 }, { 'x': 21, 'y': 29 }, { 'x': 26, 'y': 29 }, { 'x': 21, 'y': 30 }, { 'x': 26, 'y': 30 }, { 'x': 21, 'y': 31 }, { 'x': 22, 'y': 31 }, { 'x': 23, 'y': 31 }, { 'x': 24, 'y': 31 }, { 'x': 25, 'y': 31 }, { 'x': 26, 'y': 31 }] }, 'nuker': { 'pos': [{ 'x': 22, 'y': 25 }] }, 'powerSpawn': { 'pos': [{ 'x': 23, 'y': 25 }] }, 'link': { 'pos': [{ 'x': 24, 'y': 25 }] }, 'storage': { 'pos': [{ 'x': 25, 'y': 25 }] }, 'observer': { 'pos': [{ 'x': 22, 'y': 26 }] }, 'terminal': { 'pos': [{ 'x': 25, 'y': 26 }] }, 'tower': { 'pos': [{ 'x': 23, 'y': 27 }, { 'x': 24, 'y': 27 }] }, 'lab': { 'pos': [{ 'x': 23, 'y': 28 }, { 'x': 24, 'y': 28 }, { 'x': 22, 'y': 29 }, { 'x': 23, 'y': 29 }, { 'x': 24, 'y': 29 }, { 'x': 25, 'y': 29 }, { 'x': 22, 'y': 30 }, { 'x': 23, 'y': 30 }, { 'x': 24, 'y': 30 }, { 'x': 25, 'y': 30 }] } } }, };

const asciiLogo = ['___________________________________________________________',
    '',
    ' _____  _    _ _______  ______ _______ _____ __   _ ______ ',
    '|     |  \\  /  |______ |_____/ |  |  |   |   | \\  | |     \\',
    '|_____|   \\/   |______ |    \\_ |  |  | __|__ |  \\_| |_____/',
    '',
    '_______________________ Screeps AI ________________________'];
const asciiLogoSmall = [' _____  _    _ _______  ______ _______ _____ __   _ ______ ',
    '|     |  \\  /  |______ |_____/ |  |  |   |   | \\  | |     \\',
    '|_____|   \\/   |______ |    \\_ |  |  | __|__ |  \\_| |_____/'];
const _logoComponents = {
    black: {
        style: { fill: '#000000', stroke: '#000000', strokeWidth: 0 },
        points: [[-4.4, -0.34], [-3.44, -1.04], [-3.08, -1.04], [-2.78, -0.82], [-2.7, -0.6], [-2.92, -0.24], [-3.36, -0.24], [-3.58, -0.5], [-3.8, -0.28], [-4.14, 0.42], [-4.22, 1.24], [-3.6, 0.42], [-2.98, 0.46], [-2.84, 0.72], [-2.9, 1.02], [-3.26, 1.22], [-3.68, 1.12], [-3.72, 1.22], [-3.76, 2.18], [-3.58, 2.9], [-3.22, 1.8], [-2.72, 1.66], [-2.4, 2.08], [-2.64, 2.44], [-3.1, 2.42], [-3.1, 2.86], [-2.86, 3.4], [-2.52, 3.74], [-2.58, 3.08], [-2.34, 2.86], [-1.98, 2.82], [-1.48, 3.12], [-1.34, 3.72], [-1.64, 4.16], [-2.08, 4.32], [-2.78, 4.24], [-3.4, 3.84], [-3.02, 4.34], [-2.56, 4.6], [-0.94, 4.78], [4.0e-2, 4.5], [0.86, 3.9], [-0.44, 3.18], [-0.46, 2.86], [0.88, 2.84], [2.02, 3.2], [3.1, 2.22], [4.18, 0.6], [4.54, -1], [3.84, 0], [3.5, 0.12], [3.18, 2.0e-2], [3.14, -0.46], [3.38, -0.6], [3.82, -0.5], [4, -0.94], [4.08, -1.88], [3.96, -2.6], [3.56, -1.54], [3.16, -1.22], [2.78, -1.28], [2.6, -1.6], [2.7, -1.88], [2.96, -2.02], [3.4, -1.92], [3.46, -2.12], [3.38, -2.98], [2.9, -3.98], [2.52, -4.32], [2.7, -3.58], [2.54, -2.82], [2.22, -2.38], [1.7, -2.36], [1.48, -2.64], [1.56, -3.1], [2.18, -3.24], [1.94, -3.9], [1.2, -4.62], [0.14, -5.14], [0.88, -4.18], [0.9, -3.54], [0.66, -3.04], [0.3, -2.82], [-0.14, -2.9], [-0.2, -3.42], [0.28, -3.66], [-0.38, -4.16], [-1.26, -4.32], [-2.4, -4.22], [-1.64, -4.02], [-1.08, -3.64], [-0.82, -3.04], [-0.88, -2.56], [-1.12, -2.4], [-1.5, -2.44], [-1.68, -2.7], [-1.56, -3.12], [-1.84, -3.2], [-2.72, -3.16], [-3.44, -2.84], [-3.98, -2.34], [-3.38, -2.5], [-2.48, -2.36], [-2.12, -2.12], [-2.06, -1.7], [-2.18, -1.52], [-2.56, -1.44], [-2.82, -1.6], [-2.84, -2.06], [-3.38, -1.84], [-4.06, -1.18], [-4.4, -0.36]],
    },
    blue: {
        style: { fill: '#6482B0', stroke: '#6482B0', strokeWidth: 0 },
        points: [[-2.48, -0.72], [-1.5, -0.34], [-1.18, -0.88], [-0.74, -1.24], [-6.0e-2, -1.46], [0.54, -1.44], [0.94, -1.34], [1.82, -0.46], [2.74, -0.9], [2.92, -0.42], [3.02, 0.32], [2.9, 1.02], [2.52, 1.86], [1.94, 2.5], [1.2, 2.94], [0.82, 2.02], [1.32, 1.72], [1.56, 1.48], [1.8, 1.1], [1.98, 0.44], [1.94, 0], [1.8, -0.46], [0.94, -1.36], [1.34, -2.3], [0.5, -2.54], [-0.12, -2.54], [-0.86, -2.36], [-1.38, -2.1], [-1.82, -1.76], [-2.26, -1.22], [-2.48, -0.74]],
    },
    red: {
        style: { fill: '#EA3747', stroke: '#EA3747', strokeWidth: 0 },
        points: [[0.94, -1.3], [1.28, -1.08], [1.58, -0.78], [1.78, -0.46], [2.7, -0.92], [2.72, -1], [2.44, -1.46], [2.02, -1.9], [1.42, -2.28], [0.94, -1.32]],
    },
    pink: {
        style: { fill: '#FF0080', stroke: '#FF0080', strokeWidth: 0 },
        points: [[-1.4, 0.32], [-0.92, 0.2], [-0.46, -6.0e-2], [-8.0e-2, -0.5], [0.12, -0.98], [0.14, -1.18], [0.2, -1.18], [0.22, -0.98], [0.4, -0.54], [0.8, -6.0e-2], [1.26, 0.2], [1.74, 0.32], [1.62, 0.3], [1.62, 0.36], [1.26, 0.44], [0.78, 0.72], [0.38, 1.22], [0.18, 1.84], [-6.0e-2, 1.18], [-0.46, 0.7], [-0.92, 0.44], [-1.38, 0.34]],
    },
    lgray: {
        style: { fill: '#ABB7C5', stroke: '#ABB7C5', strokeWidth: 0 },
        points: [[-2.64, 1.04], [-2.34, 1.78], [-2.06, 2.18], [-1.56, 2.64], [-0.98, 2.96], [-0.62, 3.08], [-0.52, 3.06], [-0.28, 2.06], [-0.72, 1.88], [-1.06, 1.62], [-1.36, 1.26], [-1.58, 0.76], [-2.56, 0.94], [-2.64, 1.02]],
    },
    purple: {
        style: { fill: '#2F0092', stroke: '#2F0092', strokeWidth: 0 },
        points: [[-1.48, 0.4], [-1.38, -0.24], [-1.04, -0.8], [-0.46, -1.2], [0.22, -1.32], [0.14, -1.24], [0.1, -0.94], [-8.0e-2, -0.52], [-0.42, -0.1], [-0.84, 0.16], [-1.4, 0.3], [-0.94, 0.44], [-0.34, 0.82], [4.0e-2, 1.4], [0.18, 1.88], [0.32, 1.36], [0.72, 0.78], [1.28, 0.44], [1.74, 0.34], [1.06, 0.1], [0.6, -0.26], [0.24, -0.94], [0.2, -1.24], [0.28, -1.32], [0.74, -1.22], [1.18, -0.98], [1.46, -0.7], [1.72, -0.24], [1.82, 0.26], [1.78, 0.68], [1.6, 1.14], [1.28, 1.54], [0.84, 1.82], [0.46, 1.94], [0.18, 1.98], [-0.46, 1.84], [-0.82, 1.64], [-1.22, 1.2], [-1.4, 0.82], [-1.46, 0.4]]
    },
    dgray: {
        style: { fill: '#303030', stroke: '#303030', strokeWidth: 0 },
        points: [[-2.42, 0.52], [-2.4, -8.0e-2], [-2.28, -0.56], [-1.52, -0.3], [-1.62, 0.24], [-1.58, 0.7], [-0.2, 2.06], [0.34, 2.1], [0.8, 2.02], [1.06, 2.7], [1.04, 2.78], [0.54, 2.92], [6.0e-2, 2.94], [-0.42, 2.86], [-0.22, 2.06], [-0.26, 2.08], [-1.6, 0.7], [-2.36, 0.86], [-2.4, 0.52]]
    },
};
const _logoText = {
    V: {
        coords: [75, 500],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-3.94, -3.7], [-3.72, -3.86], [-3.58, -3.68], [-1, 2.54], [-0.62, 2.9], [-0.16, 2.96], [0.46, 2.6], [3.1, -3.72], [3.38, -3.82], [3.4, -3.56], [0.86, 2.52], [0.48, 3.04], [0, 3.26], [-0.66, 3.22], [-1.26, 2.72], [-3.92, -3.68]]
    },
    E: {
        coords: [500, 880],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-4.28, 0.52], [-4.1, 1.3], [-3.7, 2.04], [-3.12, 2.64], [-2.4, 3.06], [-1.64, 3.26], [1.4, 3.2], [1.4, 3], [1.16, 2.9], [-1.5, 2.92], [-2.2, 2.76], [-3.14, 2.16], [-3.76, 1.2], [-3.92, 0.52], [-3.84, -0.12], [0.84, -0.12], [0.96, -0.24], [0.78, -0.48], [-3.9, -0.48], [-3.92, -1.12], [-3.7, -1.94], [-3.26, -2.62], [-2.6, -3.16], [-1.46, -3.52], [1.38, -3.56], [1.4, -3.8], [1.2, -3.88], [-1.42, -3.88], [-2.82, -3.44], [-3.88, -2.36], [-4.28, -1.12], [-4.26, 0.52]]
    },
    R1: {
        coords: [850, 1000],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-4.36, 3.1], [-4.36, -2.56], [-4.26, -2.96], [-3.82, -3.56], [-3.38, -3.8], [-1.88, -3.88], [-1.78, -3.5], [-3.2, -3.48], [-3.58, -3.3], [-3.88, -2.94], [-4, -2.54], [-4, 0.3], [-1.78, 0.36], [-1.9, 0.38], [-1.96, 0.72], [-1.78, 0.74], [-3.98, 0.74], [-3.98, 3.06], [-4.1, 3.26], [-4.3, 3.24], [-4.34, 3.1]]
    },
    R2: {
        coords: [1000, 1200],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-4.78, 0.74], [-4.78, 0.36], [-3.1, 0.36], [-2.22, -2.0e-2], [-1.62, -0.78], [-1.46, -1.78], [-1.74, -2.58], [-2.38, -3.22], [-3.28, -3.52], [-4.78, -3.5], [-4.7, -3.86], [-4.78, -3.88], [-3.12, -3.86], [-2.12, -3.48], [-1.62, -3.02], [-1.26, -2.42], [-1.1, -1.78], [-1.2, -0.88], [-1.56, -0.18], [-2.04, 0.3], [-2.64, 0.62], [-3.4, 0.8], [-1.22, 2.96], [-1.22, 3.24], [-1.44, 3.26], [-3.94, 0.74], [-4.76, 0.72]]
    },
    M: {
        coords: [1200, 1799],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-3.82, 3.14], [-3.6, 3.28], [-3.48, 3.08], [-2.52, -3.48], [-2.26, -3.52], [-2.1, -3.34], [0.28, 3.04], [0.56, 3.26], [0.9, 3.28], [1.3, 2.92], [3.62, -3.34], [3.88, -3.54], [4.14, -3.3], [5.02, 3.16], [5.28, 3.26], [4.44, -3.4], [4.28, -3.7], [3.98, -3.84], [3.56, -3.76], [3.34, -3.48], [1.02, 2.78], [0.78, 2.98], [0.52, 2.82], [-1.88, -3.6], [-2.24, -3.84], [-2.78, -3.68], [-3.8, 3.12]]
    },
    I: {
        coords: [1750, 1850],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-4.58, 3.1], [-4.32, 3.26], [-4.2, 3.06], [-4.2, -3.66], [-4.46, -3.86], [-4.58, -3.7], [-4.56, 3.1]]
    },
    N: {
        coords: [1850, 2250],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-4.46, 3.16], [-4.46, -3.4], [-4.34, -3.66], [-3.88, -3.88], [-3.4, -3.64], [1.52, 2.74], [1.84, 2.96], [2.12, 2.64], [2.12, -3.76], [2.36, -3.82], [2.42, 2.8], [2.28, 3.08], [1.66, 3.26], [1.38, 3.08], [-3.62, -3.4], [-3.96, -3.54], [-4.16, -3.28], [-4.16, 3.16], [-4.44, 3.18]]
    },
    D: {
        coords: [2250, 2700],
        style: { fill: '#6b6b6b', stroke: '#6b6b6b', strokeWidth: 0 },
        points: [[-4.12, 1.82], [-3.76, 2.78], [-2.8, 3.28], [-0.36, 3.24], [0.3, 3.04], [1.14, 2.5], [1.78, 1.68], [2.08, 0.84], [2.04, -1.6], [1.68, -2.44], [1.06, -3.16], [0.28, -3.64], [-0.56, -3.86], [-2.88, -3.86], [-3, -3.82], [-2.92, -3.48], [-0.32, -3.46], [0.52, -3.12], [1.2, -2.52], [1.6, -1.84], [1.78, -1.1], [1.78, 0.54], [1.38, 1.68], [0.68, 2.42], [-0.38, 2.88], [-2.78, 2.92], [-3.5, 2.54], [-3.74, 1.98], [-3.74, -2.58], [-3.46, -3.18], [-2.94, -3.48], [-3.06, -3.82], [-3.72, -3.42], [-4.08, -2.72], [-4.1, 1.8]]
    },
};
const logoX = 2.5; // x-position of logo
const logoY = 3.0; // y position of logo
const logoScale = 0.6;
const logoComponents = _.mapValues(_logoComponents, c => ({
    style: c.style,
    points: _.map(c.points, xy => [logoX + logoScale * xy[0],
        logoY + logoScale * xy[1]])
}));
const textX = logoX + 5.6 * logoScale; // x-position of logo
const textY = logoY + .5 * logoScale; // y position of logo
const textScale = 0.6 * logoScale;
const charScale = 0.052 * textScale;
let offset = 0;
const logoText = _.mapValues(_logoText, function (c) {
    let ret = {
        style: c.style,
        points: _.map(c.points, xy => [textX + textScale * (offset + xy[0]),
            textY + textScale * xy[1]])
    };
    offset += charScale * (c.coords[1] - c.coords[0]);
    return ret;
});

const textColor = '#c9c9c9';
const textSize = .8;
const charWidth = textSize * 0.4;
const charHeight = textSize * 0.9;
let Visualizer = class Visualizer {
    static get enabled() {
        return Memory.settings.enableVisuals;
    }
    static textStyle(size = 1, style = {}) {
        return _.defaults(style, {
            color: textColor,
            align: 'left',
            font: `${size * textSize} Trebuchet MS`,
            opacity: 0.8,
        });
    }
    static circle(pos, color = 'red', opts = {}) {
        _.defaults(opts, {
            fill: color,
            radius: 0.35,
            opacity: 0.5,
        });
        return new RoomVisual(pos.roomName).circle(pos.x, pos.y, opts);
    }
    static marker(pos, opts = {}) {
        return new RoomVisual(pos.roomName).animatedPosition(pos.x, pos.y, opts);
    }
    static drawStructureMap(structureMap) {
        if (!this.enabled)
            return;
        let vis = {};
        for (let structureType in structureMap) {
            for (let pos of structureMap[structureType]) {
                if (!vis[pos.roomName]) {
                    vis[pos.roomName] = new RoomVisual(pos.roomName);
                }
                vis[pos.roomName].structure(pos.x, pos.y, structureType);
            }
        }
        for (let roomName in vis) {
            vis[roomName].connectRoads();
        }
    }
    static drawLayout(layout, anchor, opts = {}) {
        _.defaults(opts, { opacity: 0.5 });
        if (!this.enabled)
            return;
        let vis = new RoomVisual(anchor.roomName);
        for (let structureType in layout[8].buildings) {
            for (let pos of layout[8].buildings[structureType].pos) {
                let dx = pos.x - layout.data.anchor.x;
                let dy = pos.y - layout.data.anchor.y;
                vis.structure(anchor.x + dx, anchor.y + dy, structureType, opts);
            }
        }
        vis.connectRoads(opts);
    }
    static drawRoads(positoins) {
        let pointsByRoom = _.groupBy(positoins, pos => pos.roomName);
        for (let roomName in pointsByRoom) {
            let vis = new RoomVisual(roomName);
            for (let pos of pointsByRoom[roomName]) {
                vis.structure(pos.x, pos.y, STRUCTURE_ROAD);
            }
            vis.connectRoads();
        }
    }
    static drawPath(path, style) {
        let pointsByRoom = _.groupBy(path, pos => pos.roomName);
        for (let roomName in pointsByRoom) {
            new RoomVisual(roomName).poly(pointsByRoom[roomName], style);
        }
    }
    static showInfo(info, calledFrom, opts = {}) {
        if (calledFrom.room) {
            return calledFrom.room.visual.infoBox(info, calledFrom.pos.x, calledFrom.pos.y, opts);
        }
        else {
            return new RoomVisual(calledFrom.pos.roomName).infoBox(info, calledFrom.pos.x, calledFrom.pos.y, opts);
        }
    }
    static section(title, pos, width, height) {
        const vis = new RoomVisual(pos.roomName);
        vis.rect(pos.x, pos.y - charHeight, width, 1.1 * charHeight, { opacity: 0.15 });
        vis.box(pos.x, pos.y - charHeight, width, height + (1.1 + .25) * charHeight, { color: textColor });
        vis.text(title, pos.x + .25, pos.y - .05, this.textStyle());
        return { x: pos.x + 0.25, y: pos.y + 1.1 * charHeight };
    }
    static infoBox(header, content, pos, width) {
        // const vis = new RoomVisual(pos.roomName);
        // vis.rect(pos.x, pos.y - charHeight, width, 1.1 * charHeight, {opacity: 0.15});
        // vis.box(pos.x, pos.y - charHeight, width, ((content.length || 1) + 1.1 + .25) * charHeight,
        // 		{color: textColor});
        // vis.text(header, pos.x + .25, pos.y - .05, this.textStyle());
        let height = charHeight * (content.length || 1);
        let { x, y } = this.section(header, pos, width, height);
        if (content.length > 0) {
            if (_.isArray(content[0])) {
                this.table(content, {
                    x: x,
                    y: y,
                    roomName: pos.roomName
                });
            }
            else {
                this.multitext(content, {
                    x: x,
                    y: y,
                    roomName: pos.roomName
                });
            }
        }
        // return pos.y - charHeight + ((content.length || 1) + 1.1 + .25) * charHeight + 0.1;
        const spaceBuffer = 0.5;
        return y + height + spaceBuffer;
    }
    static text(text, pos, size = 1, style = {}) {
        new RoomVisual(pos.roomName).text(text, pos.x, pos.y, this.textStyle(size, style));
    }
    static barGraph(progress, pos, width = 7, scale = 1) {
        const vis = new RoomVisual(pos.roomName);
        let percent;
        let mode;
        if (typeof progress === 'number') {
            percent = progress;
            mode = 'percent';
        }
        else {
            percent = progress[0] / progress[1];
            mode = 'fraction';
        }
        // Draw frame
        vis.box(pos.x, pos.y - charHeight * scale, width, 1.1 * scale * charHeight, { color: textColor });
        vis.rect(pos.x, pos.y - charHeight * scale, percent * width, 1.1 * scale * charHeight, {
            fill: textColor,
            opacity: 0.4,
            strokeWidth: 0
        });
        // Draw text
        if (mode == 'percent') {
            vis.text(`${Math.round(100 * percent)}%`, pos.x + width / 2, pos.y - .1 * charHeight, this.textStyle(1, { align: 'center' }));
        }
        else {
            let [num, den] = progress;
            vis.text(`${num}/${den}`, pos.x + width / 2, pos.y - .1 * charHeight, this.textStyle(1, { align: 'center' }));
        }
    }
    static table(data, pos) {
        if (data.length == 0) {
            return;
        }
        const colPadding = 4;
        const vis = new RoomVisual(pos.roomName);
        const style = this.textStyle();
        // Determine column locations
        let columns = Array(_.first(data).length).fill(0);
        for (let entries of data) {
            for (let i = 0; i < entries.length - 1; i++) {
                columns[i] = Math.max(columns[i], entries[i].length);
            }
        }
        // // Draw header and underline
        // vis.text(header, pos.x, pos.y, style);
        // vis.line(pos.x, pos.y + .3 * charHeight,
        // 	pos.x + charWidth * _.sum(columns) + colPadding * columns.length, pos.y + .25 * charHeight, {
        // 			 color: textColor
        // 		 });
        // Draw text
        // let dy = 1.5 * charHeight;
        let dy = 0;
        for (let entries of data) {
            let dx = 0;
            for (let i in entries) {
                vis.text(entries[i], pos.x + dx, pos.y + dy, style);
                dx += charWidth * (columns[i] + colPadding);
            }
            dy += charHeight;
        }
    }
    ;
    static multitext(lines, pos) {
        if (lines.length == 0) {
            return;
        }
        const vis = new RoomVisual(pos.roomName);
        const style = this.textStyle();
        // Draw text
        let dy = 0;
        for (let line of lines) {
            vis.text(line, pos.x, pos.y + dy, style);
            dy += charHeight;
        }
    }
    ;
    static drawHUD() {
        // Draw Overmind logo
        new RoomVisual().multitext(asciiLogo, 0, 0, { textfont: 'monospace' });
        // // Display CPU Information
        // new RoomVisual().text('CPU:' + ' bucket:' + Game.cpu.bucket +
        // 					  ' tickLimit:' + Game.cpu.tickLimit, column, row, style);
    }
    /* Draws the Overmind logo using component coordinates extracted with Mathematica. This  uses about 0.2 CPU/tick */
    static drawLogo() {
        new RoomVisual().poly(logoComponents.black.points, logoComponents.black.style)
            .poly(logoComponents.dgray.points, logoComponents.dgray.style)
            .poly(logoComponents.lgray.points, logoComponents.lgray.style)
            .poly(logoComponents.blue.points, logoComponents.blue.style)
            .poly(logoComponents.red.points, logoComponents.red.style)
            .poly(logoComponents.purple.points, logoComponents.purple.style)
            .poly(logoComponents.pink.points, logoComponents.pink.style)
            .poly(logoText.V.points, logoText.V.style)
            .poly(logoText.E.points, logoText.E.style)
            .poly(logoText.R1.points, logoText.R1.style)
            .poly(logoText.R2.points, logoText.R2.style)
            .poly(logoText.M.points, logoText.M.style)
            .poly(logoText.I.points, logoText.I.style)
            .poly(logoText.N.points, logoText.N.style)
            .poly(logoText.D.points, logoText.D.style);
    }
    static drawNotifications(notificationMessages) {
        // const vis = new RoomVisual();
        const x = 10.5;
        const y = 7;
        if (notificationMessages.length == 0) {
            notificationMessages = ['No notifications'];
        }
        const maxStringLength = _.max(_.map(notificationMessages, msg => msg.length));
        const width = Math.max(11, 1.2 * charWidth * maxStringLength);
        this.infoBox('Notifications', notificationMessages, { x, y }, width);
    }
    // static colonyReport(colonyName: string, text: string[]) {
    // 	if (!this.enabled) return;
    // 	new RoomVisual(colonyName).multitext(text, 0, 4, {textfont: 'monospace', textsize: 0.75});
    // }
    static drawGraphs() {
        this.text(`CPU`, { x: 1, y: 7 });
        this.barGraph(Memory.stats.persistent.avgCPU / Game.cpu.limit, { x: 2.75, y: 7 });
        this.text(`BKT`, { x: 1, y: 8 });
        this.barGraph(Game.cpu.bucket / 10000, { x: 2.75, y: 8 });
        this.text(`GCL`, { x: 1, y: 9 });
        this.barGraph(Game.gcl.progress / Game.gcl.progressTotal, { x: 2.75, y: 9 });
    }
    static summary() {
        this.text(`Colonies: ${_.keys(Overmind.colonies).length} | Creeps: ${_.keys(Game.creeps).length}`, {
            x: 1,
            y: 10
        }, .93);
    }
    // This typically takes about 0.3-0.6 CPU in total
    static visuals() {
        this.drawLogo();
        this.drawGraphs();
        // this.drawNotifications();
        this.summary();
    }
};
Visualizer = __decorate([
    profile
], Visualizer);

/**
 * Operational statistics, stored in Memory.stats, will be updated every (this many) ticks
 */
const LOG_STATS_INTERVAL = 8;
let Stats = class Stats {
    static clean() {
        if (Game.time % LOG_STATS_INTERVAL == 0) {
            const protectedKeys = [
                'persistent',
            ];
            for (let key in Memory.stats) {
                if (!protectedKeys.includes(key)) {
                    delete Memory.stats[key];
                }
            }
        }
    }
    static log(key, value, truncateNumbers = true) {
        if (Game.time % LOG_STATS_INTERVAL == 0) {
            if (truncateNumbers && value != undefined) {
                const decimals = 5;
                if (typeof value == 'number') {
                    value = value.truncate(decimals);
                }
                else {
                    for (let i in value) {
                        value[i] = value[i].truncate(decimals);
                    }
                }
            }
            Mem.setDeep(Memory.stats, key, value);
        }
    }
    // static accumulate(key: string, value: number): void {
    // 	if (!Memory.stats[key]) {
    // 		Memory.stats[key] = 0;
    // 	}
    // 	Memory.stats[key] += value;
    // }
    static run() {
        if (Game.time % LOG_STATS_INTERVAL == 0) {
            // Record IVM heap statistics
            Memory.stats['cpu.heapStatistics'] = Game.cpu.getHeapStatistics();
            // Log GCL
            this.log('gcl.progress', Game.gcl.progress);
            this.log('gcl.progressTotal', Game.gcl.progressTotal);
            this.log('gcl.level', Game.gcl.level);
            // Log memory usage
            this.log('memory.used', RawMemory.get().length);
            // Log CPU
            this.log('cpu.limit', Game.cpu.limit);
            this.log('cpu.bucket', Game.cpu.bucket);
        }
        const used = Game.cpu.getUsed();
        this.log('cpu.getUsed', used);
        Memory.stats.persistent.avgCPU = exponentialMovingAverage(used, Memory.stats.persistent.avgCPU, 100);
    }
};
Stats = __decorate([
    profile
], Stats);

var Mem_1;
var Autonomy;
(function (Autonomy) {
    Autonomy[Autonomy["Manual"] = 0] = "Manual";
    Autonomy[Autonomy["SemiAutomatic"] = 1] = "SemiAutomatic";
    Autonomy[Autonomy["Automatic"] = 2] = "Automatic";
})(Autonomy || (Autonomy = {}));
function getAutonomyLevel() {
    switch (Memory.settings.operationMode) {
        case ('manual'):
            return Autonomy.Manual;
        case ('semiautomatic'):
            return Autonomy.SemiAutomatic;
        case ('automatic'):
            return Autonomy.Automatic;
        default:
            log.warning(`ERROR: ${Memory.settings.operationMode} is not a valid operation mode! ` +
                `Defaulting to ${DEFAULT_OPERATION_MODE}; use setMode() to change.`);
            Memory.settings.operationMode = DEFAULT_OPERATION_MODE;
            return getAutonomyLevel();
    }
}
// ††
let lastMemory;
let lastTime = 0;
const MAX_BUCKET = 10000;
let Mem = Mem_1 = class Mem {
    static shouldRun() {
        let shouldRun = true;
        if (!isIVM()) {
            log.warning(`Overmind requires isolated-VM to run. Change settings at screeps.com/a/#!/account/runtime`);
            shouldRun = false;
        }
        if (USE_PROFILER && Game.time % 10 == 0) {
            log.warning(`Profiling is currently enabled; only ${PROFILER_COLONY_LIMIT} colonies will be run!`);
        }
        if (Game.cpu.bucket < 10) {
            if (_.keys(Game.spawns).length > 1) { // don't run CPU reset routine at very beginning
                log.warning(`CPU bucket is critically low (${Game.cpu.bucket})! Starting CPU reset routine.`);
                Memory.resetBucket = true;
                Memory.haltTick = Game.time + 1; // reset global next tick
            }
            else {
                log.info(`CPU bucket is very (${Game.cpu.bucket}).`);
            }
            shouldRun = false;
        }
        if (Memory.resetBucket) {
            if (Game.cpu.bucket < MAX_BUCKET-7500 - Game.cpu.limit) {
                log.info(`Bucket somewhat low. Bucket: ${Game.cpu.bucket}/${MAX_BUCKET}`);
            }
            else {
                delete Memory.resetBucket;
            }
        }
        if (Memory.haltTick) {
            if (Memory.haltTick == Game.time) {
                Game.cpu.halt(); // TODO: remove any typing when typed-screeps updates to include this method
                shouldRun = false;
            }
            else if (Memory.haltTick < Game.time) {
                delete Memory.haltTick;
            }
        }
        return shouldRun;
    }
    /* Attempt to load the parsed memory from a previous tick to avoid parsing costs */
    static load() {
        if (lastTime && lastMemory && Game.time == lastTime + 1) {
            delete global.Memory;
            global.Memory = lastMemory;
            RawMemory._parsed = lastMemory;
        }
        else {
            // noinspection TsLint
            Memory.rooms; // forces parsing
            lastMemory = RawMemory._parsed;
            Memory.stats.persistent.lastMemoryReset = Game.time;
        }
        lastTime = Game.time;
        // Handle global time
        if (!global.age) {
            global.age = 0;
        }
        global.age++;
        Memory.stats.persistent.globalAge = global.age;
    }
    static garbageCollect(quick) {
        if (global.gc) { // sometimes garbage collection isn't available
            let start = Game.cpu.getUsed();
            global.gc(quick);
            log.debug(`Running ${quick ? 'quick' : 'FULL'} garbage collection. ` +
                `Elapsed time: ${Game.cpu.getUsed() - start}.`);
        }
        else {
            log.debug(`Manual garbage collection is unavailable on this server.`);
        }
    }
    static wrap(memory, memName, defaults = {}, deep = false) {
        if (!memory[memName]) {
            memory[memName] = _.clone(defaults);
        }
        if (deep) {
            _.defaultsDeep(memory[memName], defaults);
        }
        else {
            _.defaults(memory[memName], defaults);
        }
        return memory[memName];
    }
    static _setDeep(object, keys, value) {
        let key = _.first(keys);
        keys = _.drop(keys);
        if (keys.length == 0) { // at the end of the recursion
            object[key] = value;
            return;
        }
        else {
            if (!object[key]) {
                object[key] = {};
            }
            return Mem_1._setDeep(object[key], keys, value);
        }
    }
    /* Recursively set a value of an object given a dot-separated key, adding intermediate properties as necessary
     * Ex: Mem.setDeep(Memory.colonies, 'E1S1.miningSites.siteID.stats.uptime', 0.5) */
    static setDeep(object, keyString, value) {
        let keys = keyString.split('.');
        return Mem_1._setDeep(object, keys, value);
    }
    static formatOvermindMemory() {
        if (!Memory.Overmind) {
            Memory.Overmind = {};
        }
        if (!Memory.colonies) {
            Memory.colonies = {};
        }
    }
    static formatPathingMemory() {
        if (!Memory.pathing) {
            Memory.pathing = {}; // Hacky workaround
        }
        _.defaults(Memory.pathing, {
            paths: {},
            distances: {},
            weightedDistances: {},
        });
    }
    static format() {
        // Format the memory as needed, done once every global reset
        this.formatOvermindMemory();
        this.formatPathingMemory();
        // Rest of memory formatting
        if (!Memory.settings) {
            Memory.settings = {};
        }
        if (!USE_PROFILER) {
            delete Memory.profiler;
        }
        _.defaults(Memory.settings, {
            signature: DEFAULT_OVERMIND_SIGNATURE,
            operationMode: DEFAULT_OPERATION_MODE,
            log: {},
            enableVisuals: true,
        });
        if (!Memory.stats) {
            Memory.stats = {};
        }
        if (!Memory.stats.persistent) {
            Memory.stats.persistent = {};
        }
        if (!Memory.constructionSites) {
            Memory.constructionSites = {};
        }
        // Make global memory
        this.initGlobalMemory();
    }
    static initGlobalMemory() {
        global._cache = {
            accessed: {},
            expiration: {},
            structures: {},
            numbers: {},
            lists: {},
            costMatrices: {},
            roomPositions: {},
            things: {},
        };
    }
    static cleanCreeps() {
        // Clear memory for non-existent creeps
        for (let name in Memory.creeps) {
            if (!Game.creeps[name]) {
                delete Memory.creeps[name];
                delete global[name];
            }
        }
    }
    static cleanFlags() {
        // Clear memory for non-existent flags
        for (let name in Memory.flags) {
            if (!Game.flags[name]) {
                delete Memory.flags[name];
            }
        }
    }
    static cleanColonies() {
        // Clear memory of dead colonies
        for (let name in Memory.colonies) {
            let room = Game.rooms[name];
            if (!(room && room.my)) {
                // Delete only if "persistent" is not set - use case: praise rooms
                if (!Memory.colonies[name].persistent) {
                    delete Memory.colonies[name];
                }
            }
        }
    }
    static cleanConstructionSites() {
        // Remove ancient construction sites
        if (Game.time % 10 == 0) {
            const CONSTRUCTION_SITE_TIMEOUT = 50000;
            // Add constructionSites to memory and remove really old ones
            for (let id in Game.constructionSites) {
                const site = Game.constructionSites[id];
                if (!Memory.constructionSites[id]) {
                    Memory.constructionSites[id] = Game.time;
                }
                else if (Game.time - Memory.constructionSites[id] > CONSTRUCTION_SITE_TIMEOUT) {
                    site.remove();
                }
                // Remove duplicate construction sites that get placed on top of existing structures due to caching
                if (site && site.pos.isVisible && site.pos.lookForStructure(site.structureType)) {
                    site.remove();
                }
            }
            // Remove dead constructionSites from memory
            for (let id in Memory.constructionSites) {
                if (!Game.constructionSites[id]) {
                    delete Memory.constructionSites[id];
                }
            }
        }
    }
    static cleanPathingMemory() {
        const CLEAN_FREQUENCY = 5;
        if (Game.time % CLEAN_FREQUENCY == 0) {
            const distanceCleanProbability = 0.001 * CLEAN_FREQUENCY;
            const weightedDistanceCleanProbability = 0.01 * CLEAN_FREQUENCY;
            // Randomly clear some cached path lengths
            for (let pos1Name in Memory.pathing.distances) {
                if (_.isEmpty(Memory.pathing.distances[pos1Name])) {
                    delete Memory.pathing.distances[pos1Name];
                }
                else {
                    for (let pos2Name in Memory.pathing.distances[pos1Name]) {
                        if (Math.random() < distanceCleanProbability) {
                            delete Memory.pathing.distances[pos1Name][pos2Name];
                        }
                    }
                }
            }
            // Randomly clear weighted distances
            for (let pos1Name in Memory.pathing.weightedDistances) {
                if (_.isEmpty(Memory.pathing.weightedDistances[pos1Name])) {
                    delete Memory.pathing.weightedDistances[pos1Name];
                }
                else {
                    for (let pos2Name in Memory.pathing.weightedDistances[pos1Name]) {
                        if (Math.random() < weightedDistanceCleanProbability) {
                            delete Memory.pathing.weightedDistances[pos1Name][pos2Name];
                        }
                    }
                }
            }
        }
    }
    static clean() {
        // Clean the memory of non-existent objects every tick
        this.cleanCreeps();
        this.cleanFlags();
        this.cleanColonies();
        this.cleanPathingMemory();
        this.cleanConstructionSites();
        Stats.clean();
    }
};
Mem = Mem_1 = __decorate([
    profile
], Mem);

/* Generalized class for a base component */
let HiveCluster = class HiveCluster {
    constructor(colony, instantiationObject, name, includePos = false) {
        // Set up hatchery, register colony and memory
        this.colony = colony;
        this.room = instantiationObject.room;
        this.pos = instantiationObject.pos;
        // this.componentName = name;
        this.ref = includePos ? name + '@' + instantiationObject.pos.name : name + '@' + this.colony.name;
        this.colony.hiveClusters.push(this);
    }
    get print() {
        return '<a href="#!/room/' + Game.shard.name + '/' + this.pos.roomName + '">[' + this.ref + ']</a>';
    }
};
HiveCluster = __decorate([
    profile
], HiveCluster);

let Tasks = class Tasks {
    static chain(tasks, setNextPos = true) {
        if (tasks.length == 0) {
            // log.error(`Tasks.chain was passed an empty array of tasks!`);
            return null;
        }
        if (setNextPos) {
            for (let i = 0; i < tasks.length - 1; i++) {
                tasks[i].options.nextPos = tasks[i + 1].targetPos;
            }
        }
        // Make the accumulator task from the end and iteratively fork it
        let task = _.last(tasks); // start with last task
        tasks = _.dropRight(tasks); // remove it from the list
        for (let i = (tasks.length - 1); i >= 0; i--) { // iterate over the remaining tasks
            task = task.fork(tasks[i]);
        }
        return task;
    }
    static attack(target, options = {}) {
        return new TaskAttack(target, options);
    }
    static build(target, options = {}) {
        return new TaskBuild(target, options);
    }
    static claim(target, options = {}) {
        return new TaskClaim(target, options);
    }
    static dismantle(target, options = {}) {
        return new TaskDismantle(target, options);
    }
    static drop(target, resourceType = RESOURCE_ENERGY, amount = undefined, options = {}) {
        return new TaskDrop(target, resourceType, amount, options);
    }
    // static flee(target: fleeTargetType, options = {} as TaskOptions) {
    // 	return new TaskFlee(target, options);
    // }
    static fortify(target, options = {}) {
        return new TaskFortify(target, options);
    }
    static getBoosted(target, boostType, amount = undefined, options = {}) {
        return new TaskGetBoosted(target, boostType, amount, options);
    }
    static getRenewed(target, options = {}) {
        return new TaskGetRenewed(target, options);
    }
    static goToRoom(target, options = {}) {
        return new TaskGoToRoom(target, options);
    }
    static harvest(target, options = {}) {
        return new TaskHarvest(target, options);
    }
    static heal(target, options = {}) {
        return new TaskHeal(target, options);
    }
    static meleeAttack(target, options = {}) {
        return new TaskMeleeAttack(target, options);
    }
    static pickup(target, options = {}) {
        return new TaskPickup(target, options);
    }
    static rangedAttack(target, options = {}) {
        return new TaskRangedAttack(target, options);
    }
    static recharge(minEnergy = 0, options = {}) {
        return new TaskRecharge(null, minEnergy, options);
    }
    static repair(target, options = {}) {
        return new TaskRepair(target, options);
    }
    static reserve(target, options = {}) {
        return new TaskReserve(target, options);
    }
    static signController(target, options = {}) {
        return new TaskSignController(target, options);
    }
    static transfer(target, resourceType = RESOURCE_ENERGY, amount = undefined, options = {}) {
        return new TaskTransfer(target, resourceType, amount, options);
    }
    static transferAll(target, skipEnergy = false, options = {}) {
        return new TaskTransferAll(target, skipEnergy, options);
    }
    static upgrade(target, options = {}) {
        return new TaskUpgrade(target, options);
    }
    static withdraw(target, resourceType = RESOURCE_ENERGY, amount = undefined, options = {}) {
        return new TaskWithdraw(target, resourceType, amount, options);
    }
    static withdrawAll(target, options = {}) {
        return new TaskWithdrawAll(target, options);
    }
};
Tasks = __decorate([
    profile
], Tasks);

// Overlord: this class represents a "process" that gets executed by one or more creeps
function hasColony(initializer) {
    return initializer.colony != undefined;
}
const DEFAULT_PRESPAWN = 50;
const MAX_SPAWN_REQUESTS = 100; // this stops division by zero or related errors from sending infinite requests
const OverlordMemoryDefaults = {};
let Overlord = class Overlord {
    constructor(initializer, name, priority) {
        this.initializer = initializer;
        // this.memory = Mem.wrap(initializer.memory, name, OverlordMemoryDefaults);
        this.room = initializer.room;
        this.priority = priority;
        this.name = name;
        this.ref = initializer.ref + '>' + name;
        this.pos = initializer.pos;
        this.colony = hasColony(initializer) ? initializer.colony : initializer;
        this.spawnGroup = undefined;
        this._zerg = {};
        this._combatZerg = {};
        this.recalculateCreeps();
        this.creepUsageReport = _.mapValues(this._creeps, creep => undefined);
        this.boosts = _.mapValues(this._creeps, creep => undefined);
        // Register the overlord on the colony overseer and on the overmind
        Overmind.overlords[this.ref] = this;
        Overmind.overseer.registerOverlord(this);
    }
    get isSuspended() {
        return Overmind.overseer.isOverlordSuspended(this);
    }
    suspendFor(ticks) {
        return Overmind.overseer.suspendOverlordFor(this, ticks);
    }
    suspendUntil(untilTick) {
        return Overmind.overseer.suspendOverlordUntil(this, untilTick);
    }
    /* Refreshes overlord, recalculating creeps and refreshing existing Zerg. New creeps are automatically added,
     * and the corresponding role groups (e.g. 'queens') are automatically updated. Child methods do not need to
     * refresh their zerg properties, only other room objects stored on the Overlord. */
    refresh() {
        // // Handle suspension // TODO: finish this
        // if (this.memory.suspendUntil) {
        // 	if (Game.time < this.memory.suspendUntil) {
        // 		return;
        // 	} else {
        // 		delete this.memory.suspendUntil;
        // 	}
        // }
        // Refresh room
        this.room = Game.rooms[this.pos.roomName];
        // Refresh zerg
        this.recalculateCreeps();
        for (let role in this._creeps) {
            for (let creep of this._creeps[role]) {
                if (Overmind.zerg[creep.name]) {
                    // log.debug(`Refreshing creep ${creep.name}`)
                    Overmind.zerg[creep.name].refresh();
                }
                else {
                    log.warning(`${this.print}: could not find and refresh zerg with name ${creep.name}!`);
                }
            }
        }
    }
    get print() {
        return '<a href="#!/room/' + Game.shard.name + '/' + this.pos.roomName + '">[' + this.ref + ']</a>';
    }
    recalculateCreeps() {
        // Recalculate the sets of creeps for each role in this overlord
        this._creeps = _.mapValues(Overmind.cache.overlords[this.ref], creepsOfRole => _.map(creepsOfRole, creepName => Game.creeps[creepName]));
        // Update zerg and combatZerg records
        for (let role in this._zerg) {
            this.synchronizeZerg(role);
        }
        for (let role in this._combatZerg) {
            this.synchronizeCombatZerg(role);
        }
    }
    /* Wraps all creeps of a given role to Zerg objects and updates the contents in future ticks to avoid having to
     * explicitly refresh groups of Zerg */
    zerg(role, opts = {}) {
        if (!this._zerg[role]) {
            this._zerg[role] = [];
            this.synchronizeZerg(role, opts.notifyWhenAttacked);
        }
        if (opts.boostWishlist) {
            this.boosts[role] = opts.boostWishlist;
        }
        return this._zerg[role];
    }
    synchronizeZerg(role, notifyWhenAttacked) {
        // Synchronize the corresponding sets of Zerg
        let zergNames = _.zipObject(_.map(this._zerg[role] || [], zerg => [zerg.name, true]));
        let creepNames = _.zipObject(_.map(this._creeps[role] || [], creep => [creep.name, true]));
        // Add new creeps which aren't in the _zerg record
        for (let creep of this._creeps[role] || []) {
            if (!zergNames[creep.name]) {
                this._zerg[role].push(Overmind.zerg[creep.name] || new Zerg(creep, notifyWhenAttacked));
            }
        }
        // Remove dead/reassigned creeps from the _zerg record
        for (let zerg of this._zerg[role]) {
            if (!creepNames[zerg.name]) {
                _.remove(this._zerg[role], z => z.name == zerg.name);
            }
        }
    }
    /* Wraps all creeps of a given role to CombatZerg objects and updates the contents in future ticks */
    combatZerg(role, opts = {}) {
        if (!this._combatZerg[role]) {
            this._combatZerg[role] = [];
            this.synchronizeCombatZerg(role, opts.notifyWhenAttacked);
        }
        if (opts.boostWishlist) {
            this.boosts[role] = opts.boostWishlist;
        }
        return this._combatZerg[role];
    }
    synchronizeCombatZerg(role, notifyWhenAttacked) {
        // Synchronize the corresponding sets of CombatZerg
        let zergNames = _.zipObject(_.map(this._combatZerg[role] || [], zerg => [zerg.name, true]));
        let creepNames = _.zipObject(_.map(this._creeps[role] || [], creep => [creep.name, true]));
        // Add new creeps which aren't in the _combatZerg record
        for (let creep of this._creeps[role] || []) {
            if (!zergNames[creep.name]) {
                if (Overmind.zerg[creep.name] && Overmind.zerg[creep.name].isCombatZerg) {
                    this._combatZerg[role].push(Overmind.zerg[creep.name]);
                }
                else {
                    this._combatZerg[role].push(new CombatZerg(creep, notifyWhenAttacked));
                }
            }
        }
        // Remove dead/reassigned creeps from the _combatZerg record
        for (let zerg of this._combatZerg[role]) {
            if (!creepNames[zerg.name]) {
                _.remove(this._combatZerg[role], z => z.name == zerg.name);
            }
        }
    }
    /* Gets the "ID" of the outpost this overlord is operating in. 0 for owned rooms, >= 1 for outposts, -1 for other */
    get outpostIndex() {
        return _.findIndex(this.colony.roomNames, this.pos.roomName);
    }
    reassignIdleCreeps(role) {
        // Find all creeps without an overlord
        let idleCreeps = _.filter(this.colony.getCreepsByRole(role), creep => !getOverlord(creep));
        // Reassign them all to this flag
        for (let creep of idleCreeps) {
            setOverlord(creep, this);
        }
    }
    // /* Returns all creeps of a specified role */
    // protected creeps(role: string): Creep[] {
    // 	if (this._creeps[role]) {
    // 		return this._creeps[role];
    // 	} else {
    // 		return [];
    // 	}
    // }
    creepReport(role, currentAmt, neededAmt) {
        this.creepUsageReport[role] = [currentAmt, neededAmt];
    }
    // TODO: include creep move speed
    lifetimeFilter(creeps, prespawn = DEFAULT_PRESPAWN) {
        let spawnDistance = 0;
        if (this.spawnGroup) {
            let distances = _.take(_.sortBy(this.spawnGroup.memory.distances), 2);
            spawnDistance = (_.sum(distances) / distances.length) || 0;
        }
        else if (this.colony.hatchery) {
            // Use distance or 0 (in case distance returns something undefined due to incomplete pathfinding)
            spawnDistance = Pathing.distance(this.pos, this.colony.hatchery.pos) || 0;
        }
        if (this.colony.isIncubating && this.colony.spawnGroup) {
            spawnDistance += this.colony.spawnGroup.stats.avgDistance;
        }
        /* The last condition fixes a bug only present on private servers that took me a fucking week to isolate.
         * At the tick of birth, creep.spawning = false and creep.ticksTolive = undefined
         * See: https://screeps.com/forum/topic/443/creep-spawning-is-not-updated-correctly-after-spawn-process */
        return _.filter(creeps, creep => creep.ticksToLive > CREEP_SPAWN_TIME * creep.body.length + spawnDistance + prespawn ||
            creep.spawning || (!creep.spawning && !creep.ticksToLive));
    }
    parkCreepsIfIdle(creeps, outsideHatchery = true) {
        for (let creep of creeps) {
            if (!creep) {
                console.log(`creeps: ${_.map(creeps, creep => creep.name)}`);
                continue;
            }
            if (creep.isIdle && creep.canExecute('move')) {
                if (this.colony.hatchery) {
                    let hatcheryRestrictedRange = 6;
                    if (creep.pos.getRangeTo(this.colony.hatchery.pos) < hatcheryRestrictedRange) {
                        let hatcheryBorder = this.colony.hatchery.pos.getPositionsAtRange(hatcheryRestrictedRange);
                        let moveToPos = creep.pos.findClosestByRange(hatcheryBorder);
                        if (moveToPos)
                            creep.goTo(moveToPos);
                    }
                    else {
                        creep.park();
                    }
                }
                else {
                    creep.park();
                }
            }
        }
    }
    /* Requests a group of (2-3) creeps from a hatchery to be spawned at the same time. Using this with low-priority
     * operations can result in a long time */
    requestSquad(setups, opts = {}) {
        log.warning(`Overlord.requestSquad() is not finished yet!`); // TODO: finish
        _.defaults(opts, { priority: this.priority, prespawn: DEFAULT_PRESPAWN });
        let spawner = this.spawnGroup || this.colony.spawnGroup || this.colony.hatchery;
        if (spawner) {
            if (setups.length > 3) {
                log.warning(`Requesting squads of >3 is not advisable`);
            }
            let request = {
                setup: _.head(setups),
                overlord: this,
                priority: opts.priority,
                partners: _.tail(setups),
            };
            if (opts.options) {
                request.options = opts.options;
            }
            spawner.enqueue(request);
        }
        else {
            if (Game.time % 100 == 0) {
                log.warning(`Overlord ${this.ref} @ ${this.pos.print}: no spawner object!`);
            }
        }
    }
    /* Create a creep setup and enqueue it to the Hatchery; does not include automatic reporting */
    requestCreep(setup, opts = {}) {
        _.defaults(opts, { priority: this.priority, prespawn: DEFAULT_PRESPAWN });
        let spawner = this.spawnGroup || this.colony.spawnGroup || this.colony.hatchery;
        if (spawner) {
            let request = {
                setup: setup,
                overlord: this,
                priority: opts.priority,
            };
            if (opts.partners) {
                request.partners = opts.partners;
            }
            if (opts.options) {
                request.options = opts.options;
            }
            spawner.enqueue(request);
        }
        else {
            if (Game.time % 100 == 0) {
                log.warning(`Overlord ${this.ref} @ ${this.pos.print}: no spawner object!`);
            }
        }
    }
    /* Wishlist of creeps to simplify spawning logic; includes automatic reporting */
    wishlist(quantity, setup, opts = {}) {
        _.defaults(opts, { priority: this.priority, prespawn: DEFAULT_PRESPAWN, reassignIdle: false });
        let creepQuantity;
        if (opts.noLifetimeFilter) {
            creepQuantity = (this._creeps[setup.role] || []).length;
        }
        else {
            creepQuantity = this.lifetimeFilter(this._creeps[setup.role] || [], opts.prespawn).length;
        }
        let spawnQuantity = quantity - creepQuantity;
        if (opts.reassignIdle && spawnQuantity > 0) {
            let idleCreeps = _.filter(this.colony.getCreepsByRole(setup.role), creep => !getOverlord(creep));
            for (let i = 0; i < Math.min(idleCreeps.length, spawnQuantity); i++) {
                setOverlord(idleCreeps[i], this);
                spawnQuantity--;
            }
        }
        // A bug in outpostDefenseOverlord caused infinite requests and cost me two botarena rounds before I found it...
        if (spawnQuantity > MAX_SPAWN_REQUESTS) {
            log.warning(`Too many requests for ${setup.role}s submitted by ${this.print}! (Check for errors.)`);
        }
        else {
            for (let i = 0; i < spawnQuantity; i++) {
                this.requestCreep(setup, opts);
            }
        }
        this.creepReport(setup.role, creepQuantity, quantity);
    }
    // TODO: finish this; currently requires host colony to have evolution chamber
    canBoostSetup(setup) {
        if (this.colony.evolutionChamber && this.boosts[setup.role] && this.boosts[setup.role].length > 0) {
            let energyCapacityAvailable;
            if (this.spawnGroup) {
                energyCapacityAvailable = this.spawnGroup.energyCapacityAvailable;
            }
            else if (this.colony.spawnGroup) {
                energyCapacityAvailable = this.colony.spawnGroup.energyCapacityAvailable;
            }
            else if (this.colony.hatchery) {
                energyCapacityAvailable = this.colony.hatchery.room.energyCapacityAvailable;
            }
            else {
                return false;
            }
            let body = _.map(setup.generateBody(energyCapacityAvailable), part => ({ type: part, hits: 100 }));
            if (body.length == 0)
                return false;
            return _.all(this.boosts[setup.role], boost => this.colony.evolutionChamber.canBoost(body, boost));
        }
        return false;
    }
    /* Return whether you are capable of boosting a creep to the desired specifications */
    shouldBoost(creep, onlyBoostInSpawn = false) {
        // Can't boost if there's no evolution chamber or TTL is less than threshold
        let colony = Overmind.colonies[creep.room.name];
        let evolutionChamber = colony ? colony.evolutionChamber : undefined;
        if (!evolutionChamber ||
            (creep.ticksToLive && creep.ticksToLive < MIN_LIFETIME_FOR_BOOST * creep.lifetime)) {
            return false;
        }
        // EDIT: they removed in-spawn boosting... RIP :(
        // // If you're in a bunker layout at level 8 with max labs, only boost while spawning
        // if (onlyBoostInSpawn && this.colony.bunker && this.colony.level == 8 && this.colony.labs.length == 10) {
        // 	if (!creep.spawning) {
        // 		return false;
        // 	}
        // }
        // Otherwise just boost if you need it and can get the resources
        if (this.boosts[creep.roleName]) {
            let boosts = _.filter(this.boosts[creep.roleName], boost => (creep.boostCounts[boost] || 0) < creep.getActiveBodyparts(boostParts[boost]));
            if (boosts.length > 0) {
                return _.all(boosts, boost => evolutionChamber.canBoost(creep.body, boost));
            }
        }
        return false;
    }
    /* Request a boost from the evolution chamber; should be called during init() */
    requestBoostsForCreep(creep) {
        let colony = Overmind.colonies[creep.room.name];
        let evolutionChamber = colony ? colony.evolutionChamber : undefined;
        if (evolutionChamber && this.boosts[creep.roleName]) {
            let boosts = _.filter(this.boosts[creep.roleName], boost => (creep.boostCounts[boost] || 0) < creep.getActiveBodyparts(boostParts[boost]));
            for (let boost of boosts) {
                evolutionChamber.requestBoost(creep, boost);
            }
        }
    }
    /* Handle boosting of a creep; should be called during run() */
    handleBoosting(creep) {
        let colony = Overmind.colonies[creep.room.name];
        let evolutionChamber = colony ? colony.evolutionChamber : undefined;
        if (this.boosts[creep.roleName] && evolutionChamber) {
            let boosts = _.filter(this.boosts[creep.roleName], boost => (creep.boostCounts[boost] || 0) < creep.getActiveBodyparts(boostParts[boost]));
            for (let boost of boosts) {
                let boostLab = _.find(evolutionChamber.boostingLabs, lab => lab.mineralType == boost);
                if (boostLab) {
                    creep.task = Tasks.getBoosted(boostLab, boost);
                }
            }
        }
    }
    /* Request any needed boosting resources from terminal network */
    requestBoosts(creeps) {
        for (let creep of creeps) {
            if (this.shouldBoost(creep)) {
                this.requestBoostsForCreep(creep);
            }
        }
    }
    /* Requests that should be handled for all overlords prior to the init() phase */
    preInit() {
        // Handle resource requests for boosts
        for (let role in this.boosts) {
            if (this.boosts[role] && this._creeps[role]) {
                this.requestBoosts(_.compact(_.map(this._creeps[role], creep => Overmind.zerg[creep.name])));
            }
        }
    }
    // Standard sequence of actions for running task-based creeps
    autoRun(roleCreeps, taskHandler, fleeCallback) {
        for (let creep of roleCreeps) {
            if (!!fleeCallback) {
                if (fleeCallback(creep))
                    continue;
            }
            if (creep.isIdle) {
                if (this.shouldBoost(creep)) {
                    this.handleBoosting(creep);
                }
                else {
                    taskHandler(creep);
                }
            }
            creep.run();
        }
    }
    visuals() {
    }
};
Overlord = __decorate([
    profile
], Overlord);
function getOverlord(creep) {
    if (creep.memory.overlord) {
        return Overmind.overlords[creep.memory.overlord] || null;
    }
    else {
        return null;
    }
}
function setOverlord(creep, newOverlord) {
    // Remove cache references to old assignments
    let roleName = creep.memory.role;
    let ref = creep.memory.overlord;
    let oldOverlord = ref ? Overmind.overlords[ref] : null;
    if (ref && Overmind.cache.overlords[ref] && Overmind.cache.overlords[ref][roleName]) {
        _.remove(Overmind.cache.overlords[ref][roleName], name => name == creep.name);
    }
    if (newOverlord) {
        // Change to the new overlord's colony
        creep.memory.colony = newOverlord.colony.name;
        // Change assignments in memory
        creep.memory.overlord = newOverlord.ref;
        // Update the cache references
        if (!Overmind.cache.overlords[newOverlord.ref]) {
            Overmind.cache.overlords[newOverlord.ref] = {};
        }
        if (!Overmind.cache.overlords[newOverlord.ref][roleName]) {
            Overmind.cache.overlords[newOverlord.ref][roleName] = [];
        }
        Overmind.cache.overlords[newOverlord.ref][roleName].push(creep.name);
    }
    else {
        creep.memory.overlord = null;
    }
    if (oldOverlord)
        oldOverlord.recalculateCreeps();
    if (newOverlord)
        newOverlord.recalculateCreeps();
    log.info(`${creep.name} has been reassigned from ${oldOverlord ? oldOverlord.print : 'IDLE'} ` +
        `to ${newOverlord ? newOverlord.print : 'IDLE'}`);
}

// Default ordering for processing spawning requests and prioritizing overlords
var OverlordPriority = {
    emergency: {
        bootstrap: 0
    },
    core: {
        queen: 100,
        manager: 101,
    },
    defense: {
        meleeDefense: 200,
        rangedDefense: 201,
    },
    warSpawnCutoff: 299,
    offense: {
        destroy: 300,
        healPoint: 301,
        siege: 302,
        controllerAttack: 399
    },
    colonization: {
        claim: 400,
        pioneer: 401,
    },
    ownedRoom: {
        firstTransport: 500,
        mine: 501,
        work: 502,
        mineralRCL8: 503,
        transport: 510,
        mineral: 520
    },
    outpostDefense: {
        outpostDefense: 550,
        guard: 551,
    },
    upgrading: {
        upgrade: 600,
    },
    throttleThreshold: 699,
    collectionUrgent: {
        haul: 700
    },
    scouting: {
        stationary: 800,
        randomWalker: 801
    },
    remoteRoom: {
        reserve: 900,
        mine: 901,
        roomIncrement: 5,
    },
    remoteSKRoom: {
        sourceReaper: 1000,
        mineral: 1001,
        mine: 1002,
        roomIncrement: 5,
    },
    collection: {
        haul: 1100
    },
    default: 99999 // Default overlord priority to ensure it gets run last
};

/* Return the cost of an entire array of body parts */
function bodyCost(bodyparts) {
    return _.sum(bodyparts, part => BODYPART_COST[part]);
}
function patternCost(setup) {
    return bodyCost(setup.bodySetup.pattern);
}
let CreepSetup = class CreepSetup {
    constructor(roleName, bodySetup = {}) {
        this.role = roleName;
        // Defaults for a creep setup
        _.defaults(bodySetup, {
            pattern: [],
            sizeLimit: Infinity,
            prefix: [],
            suffix: [],
            proportionalPrefixSuffix: false,
            ordered: true,
        });
        this.bodySetup = bodySetup;
    }
    /* Generate the largest body of a given pattern that is producable from a room,
     * subject to limitations from maxRepeats */
    generateBody(availableEnergy) {
        let patternCost, patternLength, numRepeats;
        let prefix = this.bodySetup.prefix;
        let suffix = this.bodySetup.suffix;
        let body = [];
        // calculate repetitions
        if (this.bodySetup.proportionalPrefixSuffix) { // if prefix and suffix are to be kept proportional to body size
            patternCost = bodyCost(prefix) + bodyCost(this.bodySetup.pattern) + bodyCost(suffix);
            patternLength = prefix.length + this.bodySetup.pattern.length + suffix.length;
            let energyLimit = Math.floor(availableEnergy / patternCost); // max number of repeats room can produce
            let maxPartLimit = Math.floor(MAX_CREEP_SIZE / patternLength); // max repetitions resulting in <50 parts
            numRepeats = Math.min(energyLimit, maxPartLimit, this.bodySetup.sizeLimit);
        }
        else { // if prefix and suffix don't scale
            let extraCost = bodyCost(prefix) + bodyCost(suffix);
            patternCost = bodyCost(this.bodySetup.pattern);
            patternLength = this.bodySetup.pattern.length;
            let energyLimit = Math.floor((availableEnergy - extraCost) / patternCost);
            let maxPartLimit = Math.floor((MAX_CREEP_SIZE - prefix.length - suffix.length) / patternLength);
            numRepeats = Math.min(energyLimit, maxPartLimit, this.bodySetup.sizeLimit);
        }
        // build the body
        if (this.bodySetup.proportionalPrefixSuffix) { // add the prefix
            for (let i = 0; i < numRepeats; i++) {
                body = body.concat(prefix);
            }
        }
        else {
            body = body.concat(prefix);
        }
        if (this.bodySetup.ordered) { // repeated body pattern
            for (let part of this.bodySetup.pattern) {
                for (let i = 0; i < numRepeats; i++) {
                    body.push(part);
                }
            }
        }
        else {
            for (let i = 0; i < numRepeats; i++) {
                body = body.concat(this.bodySetup.pattern);
            }
        }
        if (this.bodySetup.proportionalPrefixSuffix) { // add the suffix
            for (let i = 0; i < numRepeats; i++) {
                body = body.concat(suffix);
            }
        }
        else {
            body = body.concat(suffix);
        }
        // return it
        return body;
    }
    getBodyPotential(partType, colony) {
        // let energyCapacity = Math.max(colony.room.energyCapacityAvailable,
        // 							  colony.incubator ? colony.incubator.room.energyCapacityAvailable : 0);
        let energyCapacity = colony.room.energyCapacityAvailable;
        if (colony.spawnGroup) {
            let colonies = _.compact(_.map(colony.spawnGroup.memory.colonies, name => Overmind.colonies[name]));
            energyCapacity = _.max(_.map(colonies, colony => colony.room.energyCapacityAvailable));
        }
        let body = this.generateBody(energyCapacity);
        return _.filter(body, (part) => part == partType).length;
    }
};
CreepSetup = __decorate([
    profile
], CreepSetup);

const Roles = {
    // Civilian roles
    drone: 'drone',
    filler: 'filler',
    claim: 'infestor',
    pioneer: 'pioneer',
    manager: 'manager',
    queen: 'queen',
    scout: 'scout',
    transport: 'transport',
    worker: 'worker',
    upgrader: 'upgrader',
    // Combat roles
    guardMelee: 'broodling',
    melee: 'zergling',
    ranged: 'hydralisk',
    healer: 'transfuser',
    dismantler: 'lurker',
};
const Setups = {
    drones: {
        extractor: new CreepSetup(Roles.drone, {
            pattern: [WORK, WORK, WORK, WORK, CARRY, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
        miners: {
            default: new CreepSetup(Roles.drone, {
                pattern: [WORK, WORK, CARRY, MOVE],
                sizeLimit: 3,
            }),
            standard: new CreepSetup(Roles.drone, {
                pattern: [WORK, WORK, WORK, WORK, WORK, WORK, CARRY, MOVE, MOVE, MOVE],
                sizeLimit: 1,
            }),
            emergency: new CreepSetup(Roles.drone, {
                pattern: [WORK, WORK, CARRY, MOVE],
                sizeLimit: 1,
            }),
            double: new CreepSetup(Roles.drone, {
                pattern: [WORK, WORK, WORK, WORK, WORK, WORK, CARRY, MOVE, MOVE, MOVE],
                sizeLimit: 2,
            }),
            sourceKeeper: new CreepSetup(Roles.drone, {
                pattern: [WORK, WORK, CARRY, MOVE],
                sizeLimit: 5,
            })
        }
    },
    filler: new CreepSetup(Roles.filler, {
        pattern: [CARRY, CARRY, MOVE, MOVE],
        sizeLimit: 2,
    }),
    infestors: {
        claim: new CreepSetup(Roles.claim, {
            pattern: [MOVE, CLAIM],
            sizeLimit: 1
        }),
        reserve: new CreepSetup(Roles.claim, {
            pattern: [MOVE, CLAIM],
            sizeLimit: 4,
        }),
        controllerAttacker: new CreepSetup(Roles.claim, {
            pattern: [MOVE, CLAIM],
            sizeLimit: Infinity,
        }),
    },
    pioneer: new CreepSetup(Roles.pioneer, {
        pattern: [WORK, CARRY, CARRY, MOVE, MOVE],
        sizeLimit: Infinity,
    }),
    managers: {
        default: new CreepSetup(Roles.manager, {
            pattern: [CARRY, CARRY, CARRY, CARRY, MOVE],
            sizeLimit: 3,
        }),
        twoPart: new CreepSetup(Roles.manager, {
            pattern: [CARRY, CARRY, MOVE],
            sizeLimit: 8,
        }),
        stationary: new CreepSetup(Roles.manager, {
            pattern: [CARRY, CARRY],
            sizeLimit: 8,
        }),
        stationary_work: new CreepSetup(Roles.manager, {
            pattern: [WORK, WORK, WORK, WORK, CARRY, CARRY],
            sizeLimit: 8,
        }),
    },
    queens: {
        default: new CreepSetup(Roles.queen, {
            pattern: [CARRY, CARRY, MOVE],
            sizeLimit: Infinity,
        }),
        early: new CreepSetup(Roles.queen, {
            pattern: [CARRY, MOVE],
            sizeLimit: Infinity,
        }),
    },
    scout: new CreepSetup(Roles.scout, {
        pattern: [MOVE],
        sizeLimit: 1,
    }),
    transporters: {
        default: new CreepSetup(Roles.transport, {
            pattern: [CARRY, CARRY, MOVE],
            sizeLimit: Infinity,
        }),
        early: new CreepSetup(Roles.transport, {
            pattern: [CARRY, MOVE],
            sizeLimit: Infinity,
        }),
    },
    workers: {
        default: new CreepSetup(Roles.worker, {
            pattern: [WORK, WORK, CARRY, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
        early: new CreepSetup(Roles.worker, {
            pattern: [WORK, CARRY, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
    },
    upgraders: {
        default: new CreepSetup(Roles.upgrader, {
            pattern: [WORK, WORK, WORK, CARRY, MOVE],
            sizeLimit: Infinity,
        }),
        rcl8: new CreepSetup(Roles.upgrader, {
            pattern: [WORK, WORK, WORK, CARRY, MOVE],
            sizeLimit: 5,
        }),
    }
};
const CombatSetups = {
    // Zerglings are melee-only creeps (with exception of sourceKeeper setup)
    zerglings: {
        default: new CreepSetup(Roles.melee, {
            pattern: [ATTACK, MOVE],
            sizeLimit: Infinity,
        }),
        armored: new CreepSetup(Roles.melee, {
            pattern: [TOUGH, MOVE, MOVE, MOVE, ATTACK, ATTACK, ATTACK, MOVE],
            sizeLimit: Infinity,
        }),
        boosted_T3_defense: new CreepSetup(Roles.melee, {
            pattern: [TOUGH, ATTACK, ATTACK, ATTACK, ATTACK, ATTACK, ATTACK, ATTACK, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
        boosted_T3: new CreepSetup(Roles.melee, {
            pattern: [TOUGH, TOUGH, ATTACK, ATTACK, ATTACK, ATTACK, ATTACK, ATTACK, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
        sourceKeeper: new CreepSetup(Roles.melee, {
            pattern: [MOVE, MOVE, MOVE, MOVE, ATTACK, ATTACK, ATTACK, ATTACK, HEAL, MOVE],
            sizeLimit: Infinity,
        }),
    },
    // Hydralisks are ranged creeps which may have a small amount of healing
    hydralisks: {
        early: new CreepSetup(Roles.ranged, {
            pattern: [RANGED_ATTACK, MOVE],
            sizeLimit: Infinity,
        }),
        default: new CreepSetup(Roles.ranged, {
            pattern: [RANGED_ATTACK, RANGED_ATTACK, RANGED_ATTACK, MOVE, MOVE, MOVE, MOVE, HEAL],
            sizeLimit: Infinity,
        }),
        boosted_T3: new CreepSetup(Roles.ranged, {
            pattern: [TOUGH, TOUGH, RANGED_ATTACK, RANGED_ATTACK, RANGED_ATTACK, RANGED_ATTACK, RANGED_ATTACK,
                MOVE, MOVE, HEAL],
            sizeLimit: Infinity,
        }),
        sourceKeeper: new CreepSetup(Roles.ranged, {
            pattern: [MOVE, MOVE, MOVE, MOVE, RANGED_ATTACK, RANGED_ATTACK, RANGED_ATTACK, HEAL, HEAL, MOVE],
            sizeLimit: Infinity,
        }),
    },
    // Healers (transfusers) are creeps which only do healing
    healers: {
        default: new CreepSetup(Roles.healer, {
            pattern: [MOVE, HEAL],
            sizeLimit: Infinity,
        }),
        armored: new CreepSetup(Roles.healer, {
            pattern: [TOUGH, MOVE, MOVE, MOVE, HEAL, HEAL, HEAL, MOVE],
            sizeLimit: Infinity,
        }),
        boosted_T3: new CreepSetup(Roles.healer, {
            pattern: [TOUGH, TOUGH, HEAL, HEAL, HEAL, HEAL, HEAL, HEAL, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
    },
    // Broodlings are primarily melee creeps which may have a small amount of healing
    broodlings: {
        early: new CreepSetup(Roles.guardMelee, {
            pattern: [TOUGH, MOVE, MOVE, ATTACK],
            sizeLimit: Infinity,
        }),
        default: new CreepSetup(Roles.guardMelee, {
            pattern: [ATTACK, MOVE, MOVE, MOVE, MOVE, ATTACK, ATTACK, ATTACK, MOVE, HEAL],
            sizeLimit: Infinity,
        }),
    },
    // Dismantlers (lurkers) are creeps with work parts for dismantle sieges
    dismantlers: {
        default: new CreepSetup(Roles.dismantler, {
            pattern: [WORK, MOVE],
            sizeLimit: Infinity,
        }),
        armored: new CreepSetup(Roles.dismantler, {
            pattern: [TOUGH, MOVE, MOVE, MOVE, WORK, WORK, WORK, MOVE],
            sizeLimit: Infinity,
        }),
        boosted_T3: new CreepSetup(Roles.dismantler, {
            pattern: [TOUGH, TOUGH, WORK, WORK, WORK, WORK, WORK, WORK, MOVE, MOVE],
            sizeLimit: Infinity,
        }),
    },
};

let QueenOverlord = class QueenOverlord extends Overlord {
    constructor(hatchery, priority = OverlordPriority.core.queen) {
        super(hatchery, 'supply', priority);
        this.hatchery = hatchery;
        this.queenSetup = this.colony.storage ? Setups.queens.default : Setups.queens.early;
        this.queens = this.zerg(Roles.queen);
        this.settings = {
            refillTowersBelow: 500,
        };
    }
    init() {
        const amount = 1;
        const prespawn = this.hatchery.spawns.length <= 1 ? 100 : DEFAULT_PRESPAWN;
        this.wishlist(amount, this.queenSetup, { prespawn: prespawn });
    }
    supplyActions(queen) {
        // Select the closest supply target out of the highest priority and refill it
        let request = this.hatchery.transportRequests.getPrioritizedClosestRequest(queen.pos, 'supply');
        if (request) {
            queen.task = Tasks.transfer(request.target);
        }
        else {
            this.rechargeActions(queen); // if there are no targets, refill yourself
        }
    }
    rechargeActions(queen) {
        if (this.hatchery.link && !this.hatchery.link.isEmpty) {
            queen.task = Tasks.withdraw(this.hatchery.link);
        }
        else if (this.hatchery.battery && this.hatchery.battery.energy > 0) {
            queen.task = Tasks.withdraw(this.hatchery.battery);
        }
        else {
            queen.task = Tasks.recharge();
        }
    }
    idleActions(queen) {
        if (this.hatchery.link) {
            // Can energy be moved from the link to the battery?
            if (this.hatchery.battery && !this.hatchery.battery.isFull && !this.hatchery.link.isEmpty) {
                // Move energy to battery as needed
                if (queen.carry.energy < queen.carryCapacity) {
                    queen.task = Tasks.withdraw(this.hatchery.link);
                }
                else {
                    queen.task = Tasks.transfer(this.hatchery.battery);
                }
            }
            else {
                if (queen.carry.energy < queen.carryCapacity) { // make sure you're recharged
                    if (!this.hatchery.link.isEmpty) {
                        queen.task = Tasks.withdraw(this.hatchery.link);
                    }
                    else if (this.hatchery.battery && !this.hatchery.battery.isEmpty) {
                        queen.task = Tasks.withdraw(this.hatchery.battery);
                    }
                }
            }
        }
        else {
            if (this.hatchery.battery && queen.carry.energy < queen.carryCapacity) {
                queen.task = Tasks.withdraw(this.hatchery.battery);
            }
        }
    }
    handleQueen(queen) {
        if (queen.carry.energy > 0) {
            this.supplyActions(queen);
        }
        else {
            this.rechargeActions(queen);
        }
        // If there aren't any tasks that need to be done, recharge the battery from link
        if (queen.isIdle) {
            this.idleActions(queen);
        }
        // // If all of the above is done and hatchery is not in emergencyMode, move to the idle point and renew as needed
        // if (!this.emergencyMode && queen.isIdle) {
        // 	if (queen.pos.isEqualTo(this.idlePos)) {
        // 		// If queen is at idle position, renew her as needed
        // 		if (queen.ticksToLive < this.settings.renewQueenAt && this.availableSpawns.length > 0) {
        // 			this.availableSpawns[0].renewCreep(queen.creep);
        // 		}
        // 	} else {
        // 		// Otherwise, travel back to idle position
        // 		queen.goTo(this.idlePos);
        // 	}
        // }
    }
    run() {
        for (let queen of this.queens) {
            // Get a task
            this.handleQueen(queen);
            // Run the task if you have one; else move back to idle pos
            if (queen.hasValidTask) {
                queen.run();
            }
            else {
                if (this.queens.length > 1) {
                    queen.goTo(this.hatchery.idlePos, { range: 1 });
                }
                else {
                    queen.goTo(this.hatchery.idlePos);
                }
            }
        }
    }
};
QueenOverlord = __decorate([
    profile
], QueenOverlord);

var Priority;
(function (Priority) {
    Priority[Priority["Critical"] = 0] = "Critical";
    Priority[Priority["High"] = 1] = "High";
    Priority[Priority["NormalHigh"] = 2] = "NormalHigh";
    Priority[Priority["Normal"] = 3] = "Normal";
    Priority[Priority["NormalLow"] = 4] = "NormalLow";
    Priority[Priority["Low"] = 5] = "Low";
})(Priority || (Priority = {}));
function blankPriorityQueue() {
    let queue = {};
    for (let priority in Priority) {
        queue[priority] = [];
    }
    return queue;
}

function isSupplyStructure(structure) {
    return structure.structureType == STRUCTURE_EXTENSION
        || structure.structureType == STRUCTURE_LAB
        || structure.structureType == STRUCTURE_TOWER
        || structure.structureType == STRUCTURE_SPAWN;
}
function computeQuadrant(colony, quadrant) {
    let positions = _.map(quadrant, coord => getPosFromBunkerCoord(coord, colony));
    let structures = [];
    for (let pos of positions) {
        let structure = _.find(pos.lookFor(LOOK_STRUCTURES), s => isSupplyStructure(s));
        if (structure) {
            structures.push(structure);
        }
    }
    return structures;
}
let BunkerQueenOverlord = class BunkerQueenOverlord extends Overlord {
    constructor(hatchery, priority = OverlordPriority.core.queen) {
        super(hatchery, 'supply', priority);
        this.queenSetup = Setups.queens.default;
        this.queens = this.zerg(Roles.queen);
        this.batteries = _.filter(this.room.containers, container => insideBunkerBounds(container.pos, this.colony));
        this.storeStructures = _.compact([this.colony.terminal, this.colony.storage, ...this.batteries]);
        this.quadrants = {
            lowerRight: $.structures(this, 'LR', () => computeQuadrant(this.colony, quadrantFillOrder.lowerRight)),
            upperLeft: $.structures(this, 'UL', () => computeQuadrant(this.colony, quadrantFillOrder.upperLeft)),
            lowerLeft: $.structures(this, 'LL', () => computeQuadrant(this.colony, quadrantFillOrder.lowerLeft)),
            upperRight: $.structures(this, 'UR', () => computeQuadrant(this.colony, quadrantFillOrder.upperRight)),
        };
        this.computeQueenAssignments();
    }
    computeQueenAssignments() {
        // Assign quadrants to queens
        this.assignments = _.zipObject(_.map(this.queens, queen => [queen.name, {}]));
        const activeQueens = _.filter(this.queens, queen => !queen.spawning);
        this.numActiveQueens = activeQueens.length;
        if (this.numActiveQueens > 0) {
            let quadrantAssignmentOrder = [this.quadrants.lowerRight,
                this.quadrants.upperLeft,
                this.quadrants.lowerLeft,
                this.quadrants.upperRight];
            let i = 0;
            for (let quadrant of quadrantAssignmentOrder) {
                let queen = activeQueens[i % activeQueens.length];
                _.extend(this.assignments[queen.name], _.zipObject(_.map(quadrant, s => [s.id, true])));
                i++;
            }
        }
    }
    refresh() {
        super.refresh();
        $.refresh(this, 'batteries', 'storeStructures');
        $.refreshObject(this, 'quadrants');
        // Re-compute queen assignments if the number of queens has changed
        if (_.filter(this.queens, queen => !queen.spawning).length != this.numActiveQueens) {
            this.computeQueenAssignments();
        }
    }
    init() {
        for (let battery of this.batteries) {
            if (hasMinerals(battery.store)) { // get rid of any minerals in the container if present
                this.colony.logisticsNetwork.requestOutputMinerals(battery);
            }
        }
        // const amount = this.colony.spawns.length > 1 ? 2 : 1;
        const amount = this.colony.room.energyCapacityAvailable > 2000 ? 2 : 1;
        this.wishlist(amount, this.queenSetup);
    }
    // Builds a series of tasks to empty unnecessary carry contents, withdraw required resources, and supply structures
    buildSupplyTaskManifest(queen) {
        let tasks = [];
        // Step 1: empty all contents (this shouldn't be necessary since queen is normally empty at this point)
        let queenPos = queen.pos;
        if (_.sum(queen.carry) > 0) {
            let transferTarget = this.colony.terminal || this.colony.storage || this.batteries[0];
            if (transferTarget) {
                tasks.push(Tasks.transferAll(transferTarget));
                queenPos = transferTarget.pos;
            }
            else {
                log.warning(`No transfer targets for ${queen.print}!`);
                return null;
            }
        }
        // Step 2: figure out what you need to supply for and calculate the needed resources
        let queenCarry = {};
        let allStore = mergeSum(_.map(this.storeStructures, s => s.store));
        let supplyRequests = [];
        for (let priority in this.colony.transportRequests.supply) {
            for (let request of this.colony.transportRequests.supply[priority]) {
                if (this.assignments[queen.name][request.target.id]) {
                    supplyRequests.push(request);
                }
            }
        }
        let supplyTasks = [];
        for (let request of supplyRequests) {
            // stop when carry will be full
            let remainingAmount = queen.carryCapacity - _.sum(queenCarry);
            if (remainingAmount == 0)
                break;
            // figure out how much you can withdraw
            let amount = Math.min(request.amount, remainingAmount);
            amount = Math.min(amount, allStore[request.resourceType] || 0);
            if (amount == 0)
                continue;
            // update the simulated carry
            if (!queenCarry[request.resourceType]) {
                queenCarry[request.resourceType] = 0;
            }
            queenCarry[request.resourceType] += amount;
            // add a task to supply the target
            supplyTasks.push(Tasks.transfer(request.target, request.resourceType, amount));
        }
        // Step 3: make withdraw tasks to get the needed resources
        let withdrawTasks = [];
        let neededResources = _.keys(queenCarry);
        // TODO: a single structure doesn't need to have all resources; causes jam if labs need supply but no minerals
        let targets = _.filter(this.storeStructures, s => _.all(neededResources, resource => (s.store[resource] || 0) >= (queenCarry[resource] || 0)));
        let withdrawTarget = minBy(targets, target => Pathing.distance(queenPos, target.pos));
        if (!withdrawTarget) {
            log.warning(`Could not find adequate withdraw structure for ${queen.print}!`);
            return null;
        }
        for (let resourceType of neededResources) {
            withdrawTasks.push(Tasks.withdraw(withdrawTarget, resourceType, queenCarry[resourceType]));
        }
        // Step 4: put all the tasks in the correct order, set nextPos for each, and chain them together
        tasks = tasks.concat(withdrawTasks, supplyTasks);
        return Tasks.chain(tasks);
    }
    // Builds a series of tasks to withdraw required resources from targets
    buildWithdrawTaskManifest(queen) {
        let tasks = [];
        let transferTarget = this.colony.terminal || this.colony.storage || this.batteries[0];
        // Step 1: empty all contents (this shouldn't be necessary since queen is normally empty at this point)
        if (_.sum(queen.carry) > 0) {
            if (transferTarget) {
                tasks.push(Tasks.transferAll(transferTarget));
            }
            else {
                log.warning(`No transfer targets for ${queen.print}!`);
                return null;
            }
        }
        // Step 2: figure out what you need to withdraw from
        let queenCarry = { energy: 0 };
        // let allWithdrawRequests = _.compact(_.flatten(_.map(this.assignments[queen.name],
        // 													struc => this.transportRequests.withdrawByID[struc.id])));
        let withdrawRequests = [];
        for (let priority in this.colony.transportRequests.withdraw) {
            for (let request of this.colony.transportRequests.withdraw[priority]) {
                if (this.assignments[queen.name][request.target.id]) {
                    withdrawRequests.push(request);
                }
            }
        }
        for (let request of withdrawRequests) {
            // stop when carry will be full
            let remainingAmount = queen.carryCapacity - _.sum(queenCarry);
            if (remainingAmount == 0)
                break;
            // figure out how much you can withdraw
            let amount = Math.min(request.amount, remainingAmount);
            if (amount == 0)
                continue;
            // update the simulated carry
            if (!queenCarry[request.resourceType]) {
                queenCarry[request.resourceType] = 0;
            }
            queenCarry[request.resourceType] += amount;
            // add a task to supply the target
            tasks.push(Tasks.withdraw(request.target, request.resourceType, amount));
        }
        // Step 3: put stuff in terminal/storage
        if (transferTarget) {
            tasks.push(Tasks.transferAll(transferTarget));
        }
        else {
            log.warning(`No transfer targets for ${queen.print}!`);
            return null;
        }
        // Step 4: return chained task manifest
        return Tasks.chain(tasks);
    }
    // private getChargingSpot(queen: Zerg): RoomPosition {
    // 	let chargeSpots = _.map(bunkerChargingSpots, coord => getPosFromBunkerCoord(coord, this.colony));
    // 	let chargeSpot = (_.first(this.assignments[queen.name]) || queen).pos.findClosestByRange(chargeSpots);
    // 	if (chargeSpot) {
    // 		return chargeSpot;
    // 	} else {
    // 		log.warning(`Could not determine charging spot for queen at ${queen.pos.print}!`);
    // 		return queen.pos;
    // 	}
    // }
    //
    // private idleActions(queen: Zerg): void {
    //
    // 	// // Refill any empty batteries
    // 	// for (let battery of this.batteries) {
    // 	// 	if (!battery.isFull) {
    // 	// 		let amount = Math.min(battery.storeCapacity - _.sum(battery.store), queen.carryCapacity);
    // 	// 		let target = this.colony.storage || this.colony.storage;
    // 	// 		if (target) {
    // 	// 			queen.task = Tasks.transfer(battery, RESOURCE_ENERGY, amount)
    // 	// 							  .fork(Tasks.withdraw(target, RESOURCE_ENERGY, amount))
    // 	// 			return;
    // 	// 		}
    // 	// 	}
    // 	// }
    //
    // 	// Go to recharging spot and get recharged
    // 	let chargingSpot = this.getChargingSpot(queen);
    // 	queen.goTo(chargingSpot, {range: 0});
    // 	// // TODO: this will cause oscillating behavior where recharge drains some energy and queen leaves to supply it
    // 	// if (queen.pos.getRangeTo(chargingSpot) == 0) {
    // 	// 	let chargingSpawn = _.first(queen.pos.findInRange(this.colony.spawns, 1));
    // 	// 	if (chargingSpawn && !chargingSpawn.spawning) {
    // 	// 		chargingSpawn.renewCreep(queen.creep);
    // 	// 	}
    // 	// }
    // }
    handleQueen(queen) {
        // Does something need withdrawing?
        if (this.colony.transportRequests.needsWithdrawing &&
            _.any(_.keys(this.assignments[queen.name]), id => this.colony.transportRequests.withdrawByID[id])) {
            queen.task = this.buildWithdrawTaskManifest(queen);
        }
        // Does something need supplying?
        else if (this.colony.transportRequests.needsSupplying &&
            _.any(_.keys(this.assignments[queen.name]), id => this.colony.transportRequests.supplyByID[id])) {
            queen.task = this.buildSupplyTaskManifest(queen);
        }
        // Otherwise do idle actions
        if (queen.isIdle) {
            // this.idleActions(queen);
            delete queen.memory._go;
        }
    }
    run() {
        this.autoRun(this.queens, queen => this.handleQueen(queen));
    }
};
BunkerQueenOverlord = __decorate([
    profile
], BunkerQueenOverlord);

// Hatchery - groups all spawns and extensions in a colony
const ERR_ROOM_ENERGY_CAPACITY_NOT_ENOUGH = -20;
const ERR_SPECIFIED_SPAWN_BUSY = -21;
const HatcheryMemoryDefaults = {
    stats: {
        overload: 0,
        uptime: 0,
        longUptime: 0,
    }
};
let Hatchery = class Hatchery extends HiveCluster {
    constructor(colony, headSpawn) {
        super(colony, headSpawn, 'hatchery');
        // Register structure components
        this.memory = Mem.wrap(this.colony.memory, 'hatchery', HatcheryMemoryDefaults, true);
        if (this.colony.layout == 'twoPart')
            this.colony.destinations.push({ pos: this.pos, order: -1 });
        this.spawns = colony.spawns;
        this.availableSpawns = _.filter(this.spawns, spawn => !spawn.spawning);
        this.extensions = colony.extensions;
        this.towers = colony.commandCenter ? _.difference(colony.towers, colony.commandCenter.towers) : colony.towers;
        if (this.colony.layout == 'bunker') {
            this.battery = _.first(_.filter(this.room.containers, cont => insideBunkerBounds(cont.pos, this.colony)));
            $.set(this, 'energyStructures', () => this.computeEnergyStructures());
        }
        else {
            this.link = this.pos.findClosestByLimitedRange(colony.availableLinks, 2);
            this.colony.linkNetwork.claimLink(this.link);
            this.battery = this.pos.findClosestByLimitedRange(this.room.containers, 2);
            this.energyStructures = [].concat(this.spawns, this.extensions);
        }
        this.productionPriorities = [];
        this.productionQueue = {};
        this.isOverloaded = false;
        this.settings = {
            refillTowersBelow: 750,
            linksRequestEnergyBelow: 0,
            suppressSpawning: false,
        };
        this.transportRequests = colony.transportRequests; // hatchery always uses colony transport group
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'hatchery', HatcheryMemoryDefaults, true);
        $.refreshRoom(this);
        $.refresh(this, 'spawns', 'extensions', 'energyStructures', 'link', 'towers', 'battery');
        this.availableSpawns = _.filter(this.spawns, spawn => !spawn.spawning);
        this.isOverloaded = false;
        this.productionPriorities = [];
        this.productionQueue = {};
    }
    spawnMoarOverlords() {
        if (this.colony.layout == 'bunker' && (this.colony.storage || this.colony.terminal)
            && this.colony.assets[RESOURCE_ENERGY] > 50000) {
            this.overlord = new BunkerQueenOverlord(this); // use bunker queen if has storage and enough energy
        }
        else {
            this.overlord = new QueenOverlord(this);
        }
    }
    // Idle position for queen
    get idlePos() {
        if (this.battery) {
            return this.battery.pos;
        }
        else {
            return this.spawns[0].pos.availableNeighbors(true)[0];
        }
    }
    computeEnergyStructures() {
        if (this.colony.layout == 'bunker') {
            let positions = _.map(energyStructureOrder, coord => getPosFromBunkerCoord(coord, this.colony));
            let spawnsAndExtensions = [];
            spawnsAndExtensions = spawnsAndExtensions.concat(this.spawns, this.extensions);
            let energyStructures = [];
            for (let pos of positions) {
                let structure = _.find(pos.lookFor(LOOK_STRUCTURES), s => s.structureType == STRUCTURE_SPAWN
                    || s.structureType == STRUCTURE_EXTENSION);
                if (structure) {
                    energyStructures.push(_.remove(spawnsAndExtensions, s => s.id == structure.id)[0]);
                }
            }
            return _.compact(energyStructures.concat(spawnsAndExtensions));
        }
        else {
            // Ugly workaround to [].concat() throwing a temper tantrum
            let spawnsAndExtensions = [];
            spawnsAndExtensions = spawnsAndExtensions.concat(this.spawns, this.extensions);
            return _.sortBy(spawnsAndExtensions, structure => structure.pos.getRangeTo(this.idlePos));
        }
    }
    /* Request more energy when appropriate either via link or hauler */
    registerEnergyRequests() {
        // Register requests for input into the hatchery (goes on colony store group)
        if (this.link && this.link.isEmpty) {
            this.colony.linkNetwork.requestReceive(this.link);
        }
        if (this.battery) {
            let threshold = this.colony.stage == ColonyStage.Larva ? 0.75 : 0.5;
            if (this.battery.energy < threshold * this.battery.storeCapacity) {
                this.colony.logisticsNetwork.requestInput(this.battery, { multiplier: 1.5 });
            }
            // get rid of any minerals in the container if present
            if (hasMinerals(this.battery.store)) {
                this.colony.logisticsNetwork.requestOutputMinerals(this.battery);
            }
        }
        // Register energy transport requests (goes on hatchery store group, which can be colony store group)
        // let refillStructures = this.energyStructures;
        // if (this.colony.defcon > DEFCON.safe) {
        // 	for (let hostile of this.room.dangerousHostiles) {
        // 		// TODO: remove tranport requests if blocked by enemies
        // 	}
        // }
        // if (this.room.defcon > 0) {refillStructures = _.filter()}
        _.forEach(this.energyStructures, struct => this.transportRequests.requestInput(struct, Priority.NormalLow));
        // let refillSpawns = _.filter(this.spawns, spawn => spawn.energy < spawn.energyCapacity);
        // let refillExtensions = _.filter(this.extensions, extension => extension.energy < extension.energyCapacity);
        let refillTowers = _.filter(this.towers, tower => tower.energy < this.settings.refillTowersBelow);
        // _.forEach(refillSpawns, spawn => this.transportRequests.requestInput(spawn, Priority.NormalLow));
        // _.forEach(refillExtensions, extension => this.transportRequests.requestInput(extension, Priority.NormalLow));
        _.forEach(refillTowers, tower => this.transportRequests.requestInput(tower, Priority.NormalLow));
    }
    // Creep queueing and spawning =====================================================================================
    generateCreepName(roleName) {
        // Generate a creep name based on the role and add a suffix to make it unique
        let i = 0;
        while (Game.creeps[(roleName + '_' + i)]) {
            i++;
        }
        return (roleName + '_' + i);
    }
    ;
    spawnCreep(protoCreep, options = {}) {
        // get a spawn to use
        let spawnToUse;
        if (options.spawn) {
            spawnToUse = options.spawn;
            if (spawnToUse.spawning) {
                return ERR_SPECIFIED_SPAWN_BUSY;
            }
            else {
                _.remove(this.availableSpawns, spawn => spawn.id == spawnToUse.id); // mark as used
            }
        }
        else {
            spawnToUse = this.availableSpawns.shift();
        }
        if (spawnToUse) { // if there is a spawn, create the creep
            if (this.colony.bunker && this.colony.bunker.coreSpawn
                && spawnToUse.id == this.colony.bunker.coreSpawn.id && !options.directions) {
                options.directions = [TOP, RIGHT]; // don't spawn into the manager spot
            }
            protoCreep.name = this.generateCreepName(protoCreep.name); // modify the creep name to make it unique
            if (bodyCost(protoCreep.body) > this.room.energyCapacityAvailable) {
                return ERR_ROOM_ENERGY_CAPACITY_NOT_ENOUGH;
            }
            protoCreep.memory.data.origin = spawnToUse.pos.roomName;
            let result = spawnToUse.spawnCreep(protoCreep.body, protoCreep.name, {
                memory: protoCreep.memory,
                energyStructures: this.energyStructures,
                directions: options.directions
            });
            if (result == OK) {
                return result;
            }
            else {
                this.availableSpawns.unshift(spawnToUse); // return the spawn to the available spawns list
                return result;
            }
        }
        else { // otherwise, return busy
            return ERR_BUSY;
        }
    }
    canSpawn(body) {
        return bodyCost(body) <= this.room.energyCapacityAvailable;
    }
    canSpawnZerg(zerg) {
        return this.canSpawn(_.map(zerg.body, part => part.type));
    }
    /* Generate (but not spawn) the largest creep possible, returns the protoCreep as an object */
    generateProtoCreep(setup, overlord) {
        // Generate the creep body
        let creepBody;
        // if (overlord.colony.incubator) { // if you're being incubated, build as big a creep as you want
        // 	creepBody = setup.generateBody(overlord.colony.incubator.room.energyCapacityAvailable);
        // } else { // otherwise limit yourself to actual energy constraints
        creepBody = setup.generateBody(this.room.energyCapacityAvailable);
        // }
        // Generate the creep memory
        let creepMemory = {
            colony: overlord.colony.name,
            overlord: overlord.ref,
            role: setup.role,
            task: null,
            data: {
                origin: '',
            },
        };
        // Create the protocreep and return it
        let protoCreep = {
            body: creepBody,
            name: setup.role,
            memory: creepMemory,
        };
        return protoCreep;
    }
    /* Returns the approximate aggregated time at which the hatchery will next be available to spawn something */
    get nextAvailability() {
        if (!this._nextAvailability) {
            let allQueued = _.flatten(_.values(this.productionQueue));
            let queuedSpawnTime = _.sum(allQueued, order => order.protoCreep.body.length) * CREEP_SPAWN_TIME;
            let activeSpawnTime = _.sum(this.spawns, spawn => spawn.spawning ? spawn.spawning.remainingTime : 0);
            this._nextAvailability = (activeSpawnTime + queuedSpawnTime) / this.spawns.length;
        }
        return this._nextAvailability;
    }
    // /* Number of ticks required to make everything in spawn queue divided by number of spawns */
    // get queuedSpawnTime(): number {
    // 	if (!this._queuedSpawnTime) {
    // 		let allQueued = _.flatten(_.values(this.productionQueue)) as SpawnOrder[];
    // 		let queuedSpawnTime = _.sum(allQueued, order => order.protoCreep.body.length) * CREEP_SPAWN_TIME;
    // 		this._queuedSpawnTime = queuedSpawnTime / this.spawns.length;
    // 	}
    // 	return this._queuedSpawnTime;
    // }
    /* Enqueues a request to the hatchery */
    enqueue(request) {
        let protoCreep = this.generateProtoCreep(request.setup, request.overlord);
        let priority = request.priority;
        if (this.canSpawn(protoCreep.body) && protoCreep.body.length > 0) {
            // Spawn the creep yourself if you can
            this._nextAvailability = undefined; // invalidate cache
            // this._queuedSpawnTime = undefined;
            if (!this.productionQueue[priority]) {
                this.productionQueue[priority] = [];
                this.productionPriorities.push(priority); // this is necessary because keys interpret number as string
            }
            this.productionQueue[priority].push({ protoCreep: protoCreep, options: request.options });
        }
        else {
            log.debug(`${this.room.print}: cannot spawn creep ${protoCreep.name} with body ` +
                `${JSON.stringify(protoCreep.body)}!`);
        }
    }
    spawnHighestPriorityCreep() {
        let sortedKeys = _.sortBy(this.productionPriorities);
        for (let priority of sortedKeys) {
            // if (this.colony.defcon >= DEFCON.playerInvasion
            // 	&& !this.colony.controller.safeMode
            // 	&& priority > OverlordPriority.warSpawnCutoff) {
            // 	continue; // don't spawn non-critical creeps during wartime
            // }
            let nextOrder = this.productionQueue[priority].shift();
            if (nextOrder) {
                let { protoCreep, options } = nextOrder;
                let result = this.spawnCreep(protoCreep, options);
                if (result == OK) {
                    return result;
                }
                else if (result == ERR_SPECIFIED_SPAWN_BUSY) {
                    return result; // continue to spawn other things while waiting on specified spawn
                }
                else {
                    // If there's not enough energyCapacity to spawn, ignore it and move on, otherwise block and wait
                    if (result != ERR_ROOM_ENERGY_CAPACITY_NOT_ENOUGH) {
                        this.productionQueue[priority].unshift(nextOrder);
                        return result;
                    }
                }
            }
        }
    }
    handleSpawns() {
        // Spawn all queued creeps that you can
        while (this.availableSpawns.length > 0) {
            let result = this.spawnHighestPriorityCreep();
            if (result == ERR_NOT_ENOUGH_ENERGY) { // if you can't spawn something you want to
                this.isOverloaded = true;
            }
            if (result != OK && result != ERR_SPECIFIED_SPAWN_BUSY) {
                // Can't spawn creep right now
                break;
            }
        }
        // Move creeps off of exit position to let the spawning creep out if necessary
        for (let spawn of this.spawns) {
            if (spawn.spawning && spawn.spawning.remainingTime <= 1
                && spawn.pos.findInRange(FIND_MY_CREEPS, 1).length > 0) {
                let directions;
                if (spawn.spawning.directions) {
                    directions = spawn.spawning.directions;
                }
                else {
                    directions = _.map(spawn.pos.availableNeighbors(true), pos => spawn.pos.getDirectionTo(pos));
                }
                let exitPos = Pathing.positionAtDirection(spawn.pos, _.first(directions));
                Movement.vacatePos(exitPos);
            }
        }
    }
    // Runtime operation ===============================================================================================
    init() {
        this.registerEnergyRequests();
    }
    run() {
        if (!this.settings.suppressSpawning) {
            this.handleSpawns();
        }
        this.recordStats();
    }
    recordStats() {
        // Compute uptime and overload status
        let spawnUsageThisTick = _.filter(this.spawns, spawn => spawn.spawning).length / this.spawns.length;
        let uptime = exponentialMovingAverage(spawnUsageThisTick, this.memory.stats.uptime, CREEP_LIFE_TIME);
        let longUptime = exponentialMovingAverage(spawnUsageThisTick, this.memory.stats.longUptime, 5 * CREEP_LIFE_TIME);
        let overload = exponentialMovingAverage(this.isOverloaded ? 1 : 0, this.memory.stats.overload, CREEP_LIFE_TIME);
        Stats.log(`colonies.${this.colony.name}.hatchery.uptime`, uptime);
        Stats.log(`colonies.${this.colony.name}.hatchery.overload`, overload);
        this.memory.stats = { overload, uptime, longUptime };
    }
    visuals(coord) {
        let { x, y } = coord;
        let spawning = [];
        let spawnProgress = [];
        _.forEach(this.spawns, function (spawn) {
            if (spawn.spawning) {
                spawning.push(spawn.spawning.name.split('_')[0]);
                let timeElapsed = spawn.spawning.needTime - spawn.spawning.remainingTime;
                spawnProgress.push([timeElapsed, spawn.spawning.needTime]);
            }
        });
        let boxCoords = Visualizer.section(`${this.colony.name} Hatchery`, { x, y, roomName: this.room.name }, 9.5, 3 + spawning.length + .1);
        let boxX = boxCoords.x;
        y = boxCoords.y + 0.25;
        // Log energy
        Visualizer.text('Energy', { x: boxX, y: y, roomName: this.room.name });
        Visualizer.barGraph([this.room.energyAvailable, this.room.energyCapacityAvailable], { x: boxX + 4, y: y, roomName: this.room.name }, 5);
        y += 1;
        // Log uptime
        let uptime = this.memory.stats.uptime;
        Visualizer.text('Uptime', { x: boxX, y: y, roomName: this.room.name });
        Visualizer.barGraph(uptime, { x: boxX + 4, y: y, roomName: this.room.name }, 5);
        y += 1;
        // Log overload status
        let overload = this.memory.stats.overload;
        Visualizer.text('Overload', { x: boxX, y: y, roomName: this.room.name });
        Visualizer.barGraph(overload, { x: boxX + 4, y: y, roomName: this.room.name }, 5);
        y += 1;
        for (let i in spawning) {
            Visualizer.text(spawning[i], { x: boxX, y: y, roomName: this.room.name });
            Visualizer.barGraph(spawnProgress[i], { x: boxX + 4, y: y, roomName: this.room.name }, 5);
            y += 1;
        }
        return { x: x, y: y + .25 };
    }
};
Hatchery.restrictedRange = 6; // Don't stand idly within this range of hatchery
Hatchery = __decorate([
    profile
], Hatchery);

// Energetics manager; makes high-level decisions based on energy amounts
class Energetics {
    static lowPowerMode(colony) {
        if (colony.stage == ColonyStage.Adult) {
            if (_.sum(colony.storage.store) > this.settings.storage.total.cap &&
                colony.terminal && _.sum(colony.terminal.store) > this.settings.terminal.total.cap) {
                return true;
            }
        }
        return false;
    }
}
Energetics.settings = {
    storage: {
        total: {
            cap: STORAGE_CAPACITY - 100000
        }
    },
    terminal: {
        total: {
            cap: TERMINAL_CAPACITY - 50000
        },
        energy: {
            sendSize: 25000,
            inThreshold: 50000,
            outThreshold: 150000,
            equilibrium: 100000,
            tolerance: 5000,
        },
    },
};

// Prioritized list of what order structures should be built in
const BuildPriorities = [
    STRUCTURE_SPAWN,
    STRUCTURE_TOWER,
    STRUCTURE_EXTENSION,
    STRUCTURE_STORAGE,
    STRUCTURE_TERMINAL,
    STRUCTURE_CONTAINER,
    STRUCTURE_LINK,
    STRUCTURE_EXTRACTOR,
    STRUCTURE_LAB,
    STRUCTURE_NUKER,
    STRUCTURE_OBSERVER,
    STRUCTURE_POWER_SPAWN,
    STRUCTURE_WALL,
    STRUCTURE_RAMPART,
    STRUCTURE_ROAD,
];
// Prioritized list of what order enemy structures should be attacked in
const AttackStructurePriorities = [
    STRUCTURE_SPAWN,
    STRUCTURE_TOWER,
    STRUCTURE_EXTENSION,
    STRUCTURE_LINK,
    STRUCTURE_LAB,
    STRUCTURE_NUKER,
    STRUCTURE_OBSERVER,
    STRUCTURE_EXTRACTOR,
    STRUCTURE_POWER_SPAWN,
    STRUCTURE_CONTAINER,
    STRUCTURE_ROAD,
    STRUCTURE_STORAGE,
    STRUCTURE_TERMINAL,
    STRUCTURE_RAMPART,
    STRUCTURE_WALL,
];
const AttackStructureScores = _.zipObject(_.map(AttackStructurePriorities, type => [type, AttackStructurePriorities.length - _.indexOf(AttackStructurePriorities, type)]));
// Prioritized list of what order owned structures should be demolished (and then moved) in
const DemolishStructurePriorities = [
    { structureType: STRUCTURE_EXTENSION, maxRemoved: 15 },
    { structureType: STRUCTURE_SPAWN, maxRemoved: 1 },
    { structureType: STRUCTURE_CONTAINER },
    { structureType: STRUCTURE_TOWER, maxRemoved: 1 },
    { structureType: STRUCTURE_LINK },
    { structureType: STRUCTURE_LAB },
    { structureType: STRUCTURE_NUKER },
    { structureType: STRUCTURE_OBSERVER },
    // {structureType: STRUCTURE_EXTRACTOR, maxRemoved: 1}, // skip extractor; doesn't need to be relocated
    { structureType: STRUCTURE_POWER_SPAWN },
    // {structureType: STRUCTURE_ROAD}, // just let roads decay
    { structureType: STRUCTURE_CONTAINER },
    { structureType: STRUCTURE_STORAGE, maxRemoved: 1 },
    { structureType: STRUCTURE_TERMINAL, maxRemoved: 1 },
    { structureType: STRUCTURE_WALL },
    { structureType: STRUCTURE_RAMPART },
];

var WorkerOverlord_1;
let WorkerOverlord = WorkerOverlord_1 = class WorkerOverlord extends Overlord {
    constructor(colony, priority = OverlordPriority.ownedRoom.work) {
        super(colony, 'worker', priority);
        this.workers = this.zerg(Roles.worker);
        // Compute barriers needing fortification or critical attention
        this.fortifyBarriers = $.structures(this, 'fortifyBarriers', () => _.sortBy(_.filter(this.room.barriers, s => s.hits < WorkerOverlord_1.settings.barrierHits[this.colony.level]
            && this.colony.roomPlanner.barrierPlanner.barrierShouldBeHere(s.pos)), s => s.hits), 25);
        this.criticalBarriers = $.structures(this, 'criticalBarriers', () => _.filter(this.fortifyBarriers, barrier => barrier.hits < WorkerOverlord_1.settings.barrierHits.critical), 10);
        // Generate a list of structures needing repairing (different from fortifying except in critical case)
        this.repairStructures = $.structures(this, 'repairStructures', () => _.filter(this.colony.repairables, structure => {
            if (structure.structureType == STRUCTURE_CONTAINER) {
                // only repair containers in owned room
                if (structure.pos.roomName == this.colony.name) {
                    return structure.hits < 0.5 * structure.hitsMax;
                }
                else {
                    return false;
                }
            }
            else {
                return structure.hits < structure.hitsMax;
            }
        }));
        this.dismantleStructures = [];
        let homeRoomName = this.colony.room.name;
        let defcon = this.colony.defcon;
        // Filter constructionSites to only build valid ones
        let room = this.colony.room;
        let level = this.colony.controller.level;
        this.constructionSites = _.filter(this.colony.constructionSites, function (site) {
            // If site will be more than max amount of a structure at current level, ignore (happens after downgrade)
            let structureAmount = room[site.structureType + 's'] ? room[site.structureType + 's'].length :
                (room[site.structureType] ? 1 : 0);
            if (structureAmount >= CONTROLLER_STRUCTURES[site.structureType][level]) {
                return false;
            }
            if (defcon > DEFCON.safe) {
                // Only build non-road, non-container sites in the home room if defcon is unsafe
                return site.pos.roomName == homeRoomName &&
                    site.structureType != STRUCTURE_CONTAINER &&
                    site.structureType != STRUCTURE_ROAD;
            }
            else {
                // Build all non-container sites in outpost and all sites in room if defcon is safe
                if (site.pos.roomName != homeRoomName
                    && Cartographer.roomType(site.pos.roomName) == ROOMTYPE_CONTROLLER) {
                    return site.structureType != STRUCTURE_CONTAINER &&
                        !(site.room && site.room.dangerousHostiles.length > 0);
                }
                else {
                    return true;
                }
            }
        });
        // Nuke defense ramparts needing fortification
        if (this.room.find(FIND_NUKES).length > 0) {
            this.nukeDefenseRamparts = _.filter(this.colony.room.ramparts, function (rampart) {
                if (rampart.pos.lookFor(LOOK_NUKES).length > 0) {
                    return rampart.hits < 10000000 + 10000;
                }
                else if (rampart.pos.findInRange(FIND_NUKES, 3).length > 0) {
                    return rampart.hits < 5000000 + 10000;
                }
                else {
                    return false;
                }
            });
        }
        else {
            this.nukeDefenseRamparts = [];
        }
    }
    refresh() {
        super.refresh();
        $.refresh(this, 'repairStructures', 'dismantleStructures', 'fortifyBarriers', 'criticalBarriers', 'constructionSites', 'nukeDefenseRamparts');
    }
    init() {
        const setup = this.colony.level == 1 ? Setups.workers.early : Setups.workers.default;
        const workPartsPerWorker = setup.getBodyPotential(WORK, this.colony);
        let numWorkers;
        if (this.colony.stage == ColonyStage.Larva) {
            numWorkers = $.number(this, 'numWorkers', () => {
                // At lower levels, try to saturate the energy throughput of the colony
                const MAX_WORKERS = 10; // Maximum number of workers to spawn
                let energyMinedPerTick = _.sum(_.map(this.colony.miningSites, function (site) {
                    const overlord = site.overlords.mine;
                    const miningPowerAssigned = _.sum(overlord.miners, miner => miner.getActiveBodyparts(WORK));
                    const saturation = Math.min(miningPowerAssigned / overlord.miningPowerNeeded, 1);
                    return overlord.energyPerTick * saturation;
                }));
                let energyPerTickPerWorker = 1.1 * workPartsPerWorker; // Average energy per tick when working
                let workerUptime = 0.8;
                let numWorkers = Math.ceil(energyMinedPerTick / (energyPerTickPerWorker * workerUptime));
                return Math.min(numWorkers, MAX_WORKERS);
            });
        }
        else {
            if (this.colony.roomPlanner.memory.relocating) {
                // If relocating, maintain a maximum of workers
                numWorkers = 5;
            }
            else {
                numWorkers = $.number(this, 'numWorkers', () => {
                    // At higher levels, spawn workers based on construction and repair that needs to be done
                    const MAX_WORKERS = 5; // Maximum number of workers to spawn
                    let buildTicks = _.sum(this.constructionSites, site => Math.max(site.progressTotal - site.progress, 0)) / BUILD_POWER;
                    let repairTicks = _.sum(this.repairStructures, structure => structure.hitsMax - structure.hits) / REPAIR_POWER;
                    let paveTicks = _.sum(this.colony.rooms, room => this.colony.roadLogistics.energyToRepave(room)) / 1; // repairCost=1
                    let fortifyTicks = 0;
                    if (this.colony.assets.energy > WorkerOverlord_1.settings.fortifyDutyThreshold) {
                        fortifyTicks = 0.25 * _.sum(this.fortifyBarriers, barrier => Math.max(0, WorkerOverlord_1.settings.barrierHits[this.colony.level]
                            - barrier.hits)) / REPAIR_POWER;
                    }
                    // max constructionTicks for private server manually setting progress
                    let numWorkers = Math.ceil(2 * (5 * buildTicks + repairTicks + paveTicks + fortifyTicks) /
                        (workPartsPerWorker * CREEP_LIFE_TIME));
                    numWorkers = Math.min(numWorkers, MAX_WORKERS);
                    if (this.colony.controller.ticksToDowngrade <= (this.colony.level >= 4 ? 10000 : 2000)) {
                        numWorkers = Math.max(numWorkers, 1);
                    }
                    return numWorkers;
                });
            }
        }
        this.wishlist(numWorkers, setup);
    }
    repairActions(worker) {
        let target = worker.pos.findClosestByMultiRoomRange(this.repairStructures);
        if (target) {
            worker.task = Tasks.repair(target);
            return true;
        }
        else {
            return false;
        }
    }
    buildActions(worker) {
        let groupedSites = _.groupBy(this.constructionSites, site => site.structureType);
        for (let structureType of BuildPriorities) {
            if (groupedSites[structureType]) {
                let target = worker.pos.findClosestByMultiRoomRange(groupedSites[structureType]);
                if (target) {
                    worker.task = Tasks.build(target);
                    return true;
                }
            }
        }
        return false;
    }
    dismantleActions(worker) {
        let targets = _.filter(this.dismantleStructures, s => (s.targetedBy || []).length < 3);
        let target = worker.pos.findClosestByMultiRoomRange(targets);
        if (target) {
            _.remove(this.dismantleStructures, s => s == target);
            worker.task = Tasks.dismantle(target);
            return true;
        }
        else {
            return false;
        }
    }
    // Find a suitable repair ordering of roads with a depth first search
    buildPavingManifest(worker, room) {
        let energy = worker.carry.energy;
        let targetRefs = {};
        let tasks = [];
        let target = undefined;
        let previousPos = undefined;
        while (true) {
            if (energy <= 0)
                break;
            if (previousPos) {
                target = _.find(this.colony.roadLogistics.repairableRoads(room), road => road.hits < road.hitsMax && !targetRefs[road.id]
                    && road.pos.getRangeTo(previousPos) <= 1);
            }
            else {
                target = _.find(this.colony.roadLogistics.repairableRoads(room), road => road.hits < road.hitsMax && !targetRefs[road.id]);
            }
            if (target) {
                previousPos = target.pos;
                targetRefs[target.id] = true;
                energy -= (target.hitsMax - target.hits) / REPAIR_POWER;
                tasks.push(Tasks.repair(target));
            }
            else {
                break;
            }
        }
        return Tasks.chain(tasks);
    }
    pavingActions(worker) {
        let roomToRepave = this.colony.roadLogistics.workerShouldRepave(worker);
        this.colony.roadLogistics.registerWorkerAssignment(worker, roomToRepave);
        // Build a paving manifest
        let task = this.buildPavingManifest(worker, roomToRepave);
        if (task) {
            worker.task = task;
            return true;
        }
        else {
            return false;
        }
    }
    fortifyActions(worker, fortifyStructures = this.fortifyBarriers) {
        let lowBarriers;
        let highestBarrierHits = _.max(_.map(fortifyStructures, structure => structure.hits));
        if (highestBarrierHits > WorkerOverlord_1.settings.hitTolerance) {
            // At high barrier HP, fortify only structures that are within a threshold of the lowest
            let lowestBarrierHits = _.min(_.map(fortifyStructures, structure => structure.hits));
            lowBarriers = _.filter(fortifyStructures, structure => structure.hits <= lowestBarrierHits +
                WorkerOverlord_1.settings.hitTolerance);
        }
        else {
            // Otherwise fortify the lowest N structures
            let numBarriersToConsider = 5; // Choose the closest barrier of the N barriers with lowest hits
            lowBarriers = _.take(fortifyStructures, numBarriersToConsider);
        }
        let target = worker.pos.findClosestByMultiRoomRange(lowBarriers);
        if (target) {
            worker.task = Tasks.fortify(target);
            return true;
        }
        else {
            return false;
        }
    }
    upgradeActions(worker) {
        // Sign controller if needed
        if ((!this.colony.controller.signedByMe && !this.colony.controller.signedByScreeps)) {
            worker.task = Tasks.signController(this.colony.controller);
            return true;
        }
        worker.task = Tasks.upgrade(this.room.controller);
        return true;
    }
    handleWorker(worker) {
        if (worker.carry.energy > 0) {
            // Upgrade controller if close to downgrade
            if (this.colony.controller.ticksToDowngrade <= (this.colony.level >= 4 ? 10000 : 2000)) {
                if (this.upgradeActions(worker))
                    return;
            }
            // Repair damaged non-road non-barrier structures
            if (this.repairStructures.length > 0 && this.colony.defcon == DEFCON.safe) {
                if (this.repairActions(worker))
                    return;
            }
            // Fortify critical barriers
            if (this.criticalBarriers.length > 0) {
                if (this.fortifyActions(worker, this.criticalBarriers))
                    return;
            }
            // Build new structures
            if (this.constructionSites.length > 0) {
                if (this.buildActions(worker))
                    return;
            }
            // Build ramparts to block incoming nuke
            if (this.nukeDefenseRamparts.length > 0) {
                if (this.fortifyActions(worker, this.nukeDefenseRamparts))
                    return;
            }
            // Build and maintain roads
            if (this.colony.roadLogistics.workerShouldRepave(worker) && this.colony.defcon == DEFCON.safe) {
                if (this.pavingActions(worker))
                    return;
            }
            // Dismantle marked structures
            if (this.dismantleStructures.length > 0 && this.colony.defcon == DEFCON.safe) {
                if (this.dismantleActions(worker))
                    return;
            }
            // Fortify walls and ramparts
            if (this.fortifyBarriers.length > 0) {
                if (this.fortifyActions(worker, this.fortifyBarriers))
                    return;
            }
            // Upgrade controller if less than RCL8 or no upgraders
            if ((this.colony.level < 8 || this.colony.upgradeSite.overlord.upgraders.length == 0)
                && this.colony.defcon == DEFCON.safe) {
                if (this.upgradeActions(worker))
                    return;
            }
        }
        else {
            // Acquire more energy
            let workerWithdrawLimit = this.colony.stage == ColonyStage.Larva ? 750 : 100;
            worker.task = Tasks.recharge(workerWithdrawLimit);
        }
    }
    run() {
        this.autoRun(this.workers, worker => this.handleWorker(worker), worker => worker.flee(worker.room.fleeDefaults, { invalidateTask: true }));
    }
};
WorkerOverlord.settings = {
    barrierHits: {
        critical: 2500,
        1: 3e+3,
        2: 3e+3,
        3: 1e+4,
        4: 5e+4,
        5: 1e+5,
        6: 5e+5,
        7: 1e+6,
        8: 2e+7,
    },
    hitTolerance: 100000,
    fortifyDutyThreshold: 500000,
};
WorkerOverlord = WorkerOverlord_1 = __decorate([
    profile
], WorkerOverlord);

let CommandCenterOverlord = class CommandCenterOverlord extends Overlord {
    constructor(commandCenter, priority = OverlordPriority.core.manager) {
        super(commandCenter, 'manager', priority);
        this.commandCenter = commandCenter;
        this.mode = this.colony.layout;
        this.managers = this.zerg(Roles.manager);
        if (this.commandCenter.terminal && _.sum(this.commandCenter.terminal.store) < TERMINAL_CAPACITY - 1000) {
            this.depositTarget = this.commandCenter.terminal;
        }
        else {
            this.depositTarget = this.commandCenter.storage;
        }
        if (this.colony.bunker) {
            let anchor = this.colony.bunker.anchor;
            $.set(this, 'managerRepairTarget', () => minBy(_.filter(anchor.findInRange(anchor.room.barriers, 3), b => b.hits < WorkerOverlord.settings.barrierHits[this.colony.level]), b => b.hits));
        }
    }
    refresh() {
        super.refresh();
        $.refresh(this, 'depositTarget', 'managerRepairTarget');
    }
    init() {
        let setup = Setups.managers.default;
        let spawnRequestOptions = {};
        if (this.colony.layout == 'twoPart') {
            setup = Setups.managers.twoPart;
        }
        if (this.colony.bunker && this.colony.bunker.coreSpawn && this.colony.level == 8
            && !this.colony.roomPlanner.memory.relocating) {
            setup = Setups.managers.stationary;
            if (this.managerRepairTarget && this.colony.assets.energy > WorkerOverlord.settings.fortifyDutyThreshold) {
                setup = Setups.managers.stationary_work; // use working manager body if you have something to repair
            }
            spawnRequestOptions = {
                spawn: this.colony.bunker.coreSpawn,
                directions: [this.colony.bunker.coreSpawn.pos.getDirectionTo(this.colony.bunker.anchor)]
            };
        }
        this.wishlist(1, setup, { options: spawnRequestOptions });
    }
    unloadCarry(manager) {
        // Move anything you are currently holding to deposit location
        if (_.sum(manager.carry) > 0) {
            manager.task = Tasks.transferAll(this.depositTarget);
            return true;
        }
        else {
            return false;
        }
    }
    supplyActions(manager) {
        let request = this.commandCenter.transportRequests.getPrioritizedClosestRequest(manager.pos, 'supply');
        if (request) {
            let amount = Math.min(request.amount, manager.carryCapacity);
            manager.task = Tasks.transfer(request.target, request.resourceType, amount, { nextPos: this.commandCenter.idlePos });
            if ((manager.carry[request.resourceType] || 0) < amount) {
                // If you are currently carrying other crap, overwrite current task and put junk in terminal/storage
                if (_.sum(manager.carry) > (manager.carry[request.resourceType] || 0)) {
                    manager.task = Tasks.transferAll(this.depositTarget);
                }
                // Otherwise withdraw as much as you can hold
                else {
                    let withdrawAmount = amount - _.sum(manager.carry);
                    let withdrawFrom = this.commandCenter.storage;
                    if (this.commandCenter.terminal
                        && (request.resourceType != RESOURCE_ENERGY
                            || (withdrawFrom.store[request.resourceType] || 0) < withdrawAmount
                            || this.commandCenter.terminal.energy > Energetics.settings.terminal.energy.equilibrium)) {
                        withdrawFrom = this.commandCenter.terminal;
                    }
                    manager.task.fork(Tasks.withdraw(withdrawFrom, request.resourceType, withdrawAmount, { nextPos: request.target.pos }));
                }
            }
            return true;
        }
        return false;
    }
    withdrawActions(manager) {
        if (_.sum(manager.carry) < manager.carryCapacity) {
            let request = this.commandCenter.transportRequests.getPrioritizedClosestRequest(manager.pos, 'withdraw');
            if (request) {
                let amount = Math.min(request.amount, manager.carryCapacity - _.sum(manager.carry));
                manager.task = Tasks.withdraw(request.target, request.resourceType, amount);
                return true;
            }
        }
        else {
            manager.task = Tasks.transferAll(this.depositTarget);
            return true;
        }
        return false;
    }
    equalizeStorageAndTerminal(manager) {
        const storage = this.commandCenter.storage;
        const terminal = this.commandCenter.terminal;
        if (!storage || !terminal)
            return false;
        const equilibrium = Energetics.settings.terminal.energy.equilibrium;
        const tolerance = Energetics.settings.terminal.energy.tolerance;
        let storageEnergyCap = Energetics.settings.storage.total.cap;
        let terminalState = this.colony.terminalState;
        // Adjust max energy allowable in storage if there's an exception state happening
        if (terminalState && terminalState.type == 'out') {
            storageEnergyCap = terminalState.amounts[RESOURCE_ENERGY] || 0;
        }
        // Move energy from storage to terminal if there is not enough in terminal or if there's terminal evacuation
        if ((terminal.energy < equilibrium - tolerance || storage.energy > storageEnergyCap) && storage.energy > 0) {
            if (this.unloadCarry(manager))
                return true;
            manager.task = Tasks.withdraw(storage);
            manager.task.parent = Tasks.transfer(terminal);
            return true;
        }
        // Move energy from terminal to storage if there is too much in terminal and there is space in storage
        if (terminal.energy > equilibrium + tolerance && _.sum(storage.store) < storageEnergyCap) {
            if (this.unloadCarry(manager))
                return true;
            manager.task = Tasks.withdraw(terminal);
            manager.task.parent = Tasks.transfer(storage);
            return true;
        }
        // Nothing has happened
        return false;
    }
    moveMineralsToTerminal(manager) {
        const storage = this.commandCenter.storage;
        const terminal = this.commandCenter.terminal;
        if (!storage || !terminal) {
            return false;
        }
        // Move all non-energy resources from storage to terminal
        for (let resourceType in storage.store) {
            if (resourceType != RESOURCE_ENERGY && storage.store[resourceType] > 0) {
                if (this.unloadCarry(manager))
                    return true;
                manager.task = Tasks.withdraw(storage, resourceType);
                manager.task.parent = Tasks.transfer(terminal, resourceType);
                return true;
            }
        }
        return false;
    }
    pickupActions(manager) {
        // Pickup any resources that happen to be dropped where you are
        let resources = manager.pos.lookFor(LOOK_RESOURCES);
        if (resources.length > 0) {
            manager.task = Tasks.transferAll(this.depositTarget).fork(Tasks.pickup(resources[0]));
            return true;
        }
        // Look for tombstones at position
        let tombstones = manager.pos.lookFor(LOOK_TOMBSTONES);
        if (tombstones.length > 0) {
            manager.task = Tasks.transferAll(this.depositTarget).fork(Tasks.withdrawAll(tombstones[0]));
            return true;
        }
        return false;
    }
    // Suicide once you get old and make sure you don't drop and waste any resources
    deathActions(manager) {
        let nearbyManagers = _.filter(this.managers, manager => manager.pos.inRangeTo(this.commandCenter.pos, 3));
        if (nearbyManagers.length > 1) {
            if (_.sum(manager.carry) == 0) {
                let nearbySpawn = _.first(manager.pos.findInRange(manager.room.spawns, 1));
                if (nearbySpawn) {
                    nearbySpawn.recycleCreep(manager.creep);
                }
                else {
                    manager.suicide();
                }
            }
            else {
                manager.task = Tasks.transferAll(this.depositTarget);
            }
            return true;
        }
        return false;
    }
    handleManager(manager) {
        // Handle switching to next manager
        if (manager.ticksToLive < 150) {
            if (this.deathActions(manager))
                return;
        }
        // Pick up any dropped resources on ground
        if (this.pickupActions(manager))
            return;
        // Move minerals from storage to terminal if needed
        if (hasMinerals(this.commandCenter.storage.store)) {
            if (this.moveMineralsToTerminal(manager))
                return;
        }
        // Moving energy to terminal gets priority if evacuating room
        if (this.colony.terminalState && this.colony.terminalState.type == 'out') {
            if (this.equalizeStorageAndTerminal(manager))
                return;
        }
        // Fulfill withdraw requests
        if (this.commandCenter.transportRequests.needsWithdrawing) {
            if (this.withdrawActions(manager))
                return;
        }
        // Fulfill supply requests
        if (this.commandCenter.transportRequests.needsSupplying) {
            if (this.supplyActions(manager))
                return;
        }
        // Move energy between storage and terminal if needed
        this.equalizeStorageAndTerminal(manager);
    }
    idleActions(manager) {
        if (this.mode == 'bunker' && this.managerRepairTarget && manager.getActiveBodyparts(WORK) > 0) {
            // Repair ramparts when idle
            if (manager.carry.energy > 0) {
                manager.repair(this.managerRepairTarget);
            }
            else {
                manager.withdraw(this.depositTarget);
            }
        }
        if (!manager.pos.isEqualTo(this.commandCenter.idlePos)) {
            manager.goTo(this.commandCenter.idlePos);
        }
    }
    run() {
        for (let manager of this.managers) {
            // Get a task if needed
            if (manager.isIdle) {
                this.handleManager(manager);
            }
            // If you have a valid task, run it; else go to idle pos
            if (manager.hasValidTask) {
                manager.run();
            }
            else {
                this.idleActions(manager);
            }
        }
    }
};
CommandCenterOverlord = __decorate([
    profile
], CommandCenterOverlord);

// A stripped-down version of the logistics network intended for local deliveries
let TransportRequestGroup = class TransportRequestGroup {
    constructor() {
        this.refresh();
    }
    refresh() {
        this.supply = blankPriorityQueue();
        this.withdraw = blankPriorityQueue();
        this.supplyByID = {};
        this.withdrawByID = {};
    }
    get needsSupplying() {
        for (let priority in this.supply) {
            if (this.supply[priority].length > 0) {
                return true;
            }
        }
        return false;
    }
    get needsWithdrawing() {
        for (let priority in this.withdraw) {
            if (this.withdraw[priority].length > 0) {
                return true;
            }
        }
        return false;
    }
    getPrioritizedClosestRequest(pos, type, filter = undefined) {
        let requests = type == 'withdraw' ? this.withdraw : this.supply;
        for (let priority in requests) {
            let targets = _.map(requests[priority], request => request.target);
            let target = pos.findClosestByRangeThenPath(targets);
            if (target) {
                let searchRequests;
                if (filter) {
                    searchRequests = _.filter(requests[priority], req => filter(req));
                }
                else {
                    searchRequests = requests[priority];
                }
                return _.find(searchRequests, request => request.target.ref == target.ref);
            }
        }
    }
    /* Request for resources to be deposited into this target */
    requestInput(target, priority = Priority.Normal, opts = {}) {
        _.defaults(opts, {
            resourceType: RESOURCE_ENERGY,
        });
        if (opts.amount == undefined) {
            opts.amount = this.getInputAmount(target, opts.resourceType);
        }
        // Register the request
        let req = {
            target: target,
            resourceType: opts.resourceType,
            amount: opts.amount,
        };
        if (opts.amount > 0) {
            this.supply[priority].push(req);
            if (!this.supplyByID[target.id])
                this.supplyByID[target.id] = [];
            this.supplyByID[target.id].push(req);
        }
    }
    /* Request for resources to be withdrawn from this target */
    requestOutput(target, priority = Priority.Normal, opts = {}) {
        _.defaults(opts, {
            resourceType: RESOURCE_ENERGY,
        });
        if (opts.amount == undefined) {
            opts.amount = this.getOutputAmount(target, opts.resourceType);
        }
        // Register the request
        let req = {
            target: target,
            resourceType: opts.resourceType,
            amount: opts.amount,
        };
        if (opts.amount > 0) {
            this.withdraw[priority].push(req);
            if (!this.withdrawByID[target.id])
                this.withdrawByID[target.id] = [];
            this.withdrawByID[target.id].push(req);
        }
    }
    // /* Makes a provide for every resourceType in a requestor object */
    // requestOutputAll(target: StoreStructure, priority = Priority.Normal, opts = {} as TransportRequestOptions): void {
    // 	for (let resourceType in target.store) {
    // 		let amount = target.store[<ResourceConstant>resourceType] || 0;
    // 		if (amount > 0) {
    // 			opts.resourceType = <ResourceConstant>resourceType;
    // 			this.requestOutput(target, priority, opts);
    // 		}
    // 	}
    // }
    getInputAmount(target, resourceType) {
        if (isStoreStructure(target)) {
            return target.storeCapacity - _.sum(target.store);
        }
        else if (isEnergyStructure(target) && resourceType == RESOURCE_ENERGY) {
            return target.energyCapacity - target.energy;
        }
        else {
            if (target instanceof StructureLab) {
                if (resourceType == target.mineralType) {
                    return target.mineralCapacity - target.mineralAmount;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energyCapacity - target.energy;
                }
            }
            else if (target instanceof StructureNuker) {
                if (resourceType == RESOURCE_GHODIUM) {
                    return target.ghodiumCapacity - target.ghodium;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energyCapacity - target.energy;
                }
            }
            else if (target instanceof StructurePowerSpawn) {
                if (resourceType == RESOURCE_POWER) {
                    return target.powerCapacity - target.power;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energyCapacity - target.energy;
                }
            }
        }
        log.warning('Could not determine requestor amount!');
        return 0;
    }
    getOutputAmount(target, resourceType) {
        if (isStoreStructure(target)) {
            return target.store[resourceType];
        }
        else if (isEnergyStructure(target) && resourceType == RESOURCE_ENERGY) {
            return target.energy;
        }
        else {
            if (target instanceof StructureLab) {
                if (resourceType == target.mineralType) {
                    return target.mineralAmount;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energy;
                }
            }
            else if (target instanceof StructureNuker) {
                if (resourceType == RESOURCE_GHODIUM) {
                    return target.ghodium;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energy;
                }
            }
            else if (target instanceof StructurePowerSpawn) {
                if (resourceType == RESOURCE_POWER) {
                    return target.power;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energy;
                }
            }
        }
        log.warning('Could not determine provider amount!');
        return 0;
    }
    summarize(ignoreEnergy = false) {
        console.log(`Supply requests ==========================`);
        for (let priority in this.supply) {
            if (this.supply[priority].length > 0) {
                console.log(`Priority: ${priority}`);
            }
            for (let request of this.supply[priority]) {
                if (ignoreEnergy && request.resourceType == RESOURCE_ENERGY)
                    continue;
                console.log(`    targetID: ${request.target.ref}  amount: ${request.amount}  ` +
                    `resourceType: ${request.resourceType}`);
            }
        }
        console.log(`Withdraw requests ========================`);
        for (let priority in this.withdraw) {
            if (this.withdraw[priority].length > 0) {
                console.log(`Priority: ${priority}`);
            }
            for (let request of this.withdraw[priority]) {
                if (ignoreEnergy && request.resourceType == RESOURCE_ENERGY)
                    continue;
                console.log(`    targetID: ${request.target.ref}  amount: ${request.amount}  ` +
                    `resourceType: ${request.resourceType}`);
            }
        }
    }
};
TransportRequestGroup = __decorate([
    profile
], TransportRequestGroup);

// Command center: groups many RCL8 components, storge, lab, terminal, and some towers
var CommandCenter_1;
const MAX_OBSERVE_DISTANCE = 7;
let CommandCenter = CommandCenter_1 = class CommandCenter extends HiveCluster {
    constructor(colony, storage) {
        super(colony, storage, 'commandCenter');
        this.memory = Mem.wrap(this.colony.memory, 'commandCenter');
        // Register physical components
        this.storage = storage;
        this.terminal = colony.terminal;
        this.powerSpawn = colony.powerSpawn;
        this.nuker = colony.nuker;
        this.observer = colony.observer;
        if (this.colony.bunker) {
            this.link = this.colony.bunker.anchor.findClosestByLimitedRange(colony.availableLinks, 1);
            this.colony.linkNetwork.claimLink(this.link);
            this.towers = this.colony.bunker.anchor.findInRange(colony.towers, 1);
        }
        else {
            this.link = this.pos.findClosestByLimitedRange(colony.availableLinks, 2);
            this.colony.linkNetwork.claimLink(this.link);
            this.towers = this.pos.findInRange(colony.towers, 3);
        }
        this.terminalNetwork = Overmind.terminalNetwork;
        this.transportRequests = new TransportRequestGroup(); // commandCenter always gets its own request group
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'commandCenter');
        $.refreshRoom(this);
        $.refresh(this, 'storage', 'terminal', 'powerSpawn', 'nuker', 'observer', 'link', 'towers');
        this.transportRequests.refresh();
    }
    spawnMoarOverlords() {
        if (this.link || this.terminal) {
            this.overlord = new CommandCenterOverlord(this);
        }
    }
    // Idle position
    get idlePos() {
        if (this.colony.bunker) {
            return this.colony.bunker.anchor;
        }
        if (!this.memory.idlePos || Game.time % 25 == 0) {
            this.memory.idlePos = this.findIdlePos();
        }
        return derefRoomPosition(this.memory.idlePos);
    }
    /* Find the best idle position */
    findIdlePos() {
        // Try to match as many other structures as possible
        let proximateStructures = _.compact([this.link,
            this.terminal,
            this.powerSpawn,
            this.nuker,
            ...this.towers]);
        let numNearbyStructures = (pos) => _.filter(proximateStructures, s => s.pos.isNearTo(pos) && !s.pos.isEqualTo(pos)).length;
        return _.last(_.sortBy(this.storage.pos.neighbors, pos => numNearbyStructures(pos)));
    }
    /* Register a link transfer store if the link is sufficiently full */
    registerLinkTransferRequests() {
        if (this.link) {
            if (this.link.energy > CommandCenter_1.settings.linksTransmitAt) {
                this.colony.linkNetwork.requestTransmit(this.link);
            }
        }
    }
    registerRequests() {
        // Supply requests:
        // If the link is empty and can send energy and something needs energy, fill it up
        if (this.link && this.link.energy < 0.9 * this.link.energyCapacity && this.link.cooldown <= 1) {
            if (this.colony.linkNetwork.receive.length > 0) { // If something wants energy
                this.transportRequests.requestInput(this.link, Priority.Critical);
            }
        }
        // Refill towers as needed with variable priority
        let refillTowers = _.filter(this.towers, tower => tower.energy < CommandCenter_1.settings.refillTowersBelow);
        _.forEach(refillTowers, tower => this.transportRequests.requestInput(tower, Priority.High));
        // // Refill terminal if it is below threshold
        // if (this.terminal && this.terminal.energy < Energetics.settings.terminal.energy.inThreshold) {
        // 	this.transportRequests.requestInput(this.terminal, Priority.NormalHigh);
        // }
        // Refill core spawn (only applicable to bunker layouts)
        if (this.colony.bunker && this.colony.bunker.coreSpawn) {
            if (this.colony.bunker.coreSpawn.energy < this.colony.bunker.coreSpawn.energyCapacity) {
                this.transportRequests.requestInput(this.colony.bunker.coreSpawn, Priority.Normal);
            }
        }
        // Refill power spawn
        if (this.powerSpawn && this.powerSpawn.energy < this.powerSpawn.energyCapacity) {
            this.transportRequests.requestInput(this.powerSpawn, Priority.NormalLow);
        }
        // Refill nuker with low priority
        if (this.nuker && this.nuker.energy < this.nuker.energyCapacity && this.storage.energy > 100000) {
            this.transportRequests.requestInput(this.nuker, Priority.Low);
        }
        // Withdraw requests:
        // If the link has energy and nothing needs it, empty it
        if (this.link && this.link.energy > 0) {
            if (this.colony.linkNetwork.receive.length == 0 || this.link.cooldown > 3) {
                this.transportRequests.requestOutput(this.link, Priority.High);
            }
        }
    }
    runObserver() {
        if (this.observer) {
            let dx = Game.time % MAX_OBSERVE_DISTANCE;
            let dy = Game.time % (Math.pow(MAX_OBSERVE_DISTANCE, 2));
            let roomToObserve = Cartographer.findRelativeRoomName(this.pos.roomName, dx, dy);
            this.observer.observeRoom(roomToObserve);
        }
    }
    // Initialization and operation ====================================================================================
    init() {
        this.registerLinkTransferRequests();
        this.registerRequests();
    }
    run() {
        // this.runObserver();
    }
    visuals(coord) {
        let { x, y } = coord;
        let height = this.storage && this.terminal ? 2 : 1;
        let titleCoords = Visualizer.section(`${this.colony.name} Command Center`, { x, y, roomName: this.room.name }, 9.5, height + .1);
        let boxX = titleCoords.x;
        y = titleCoords.y + 0.25;
        if (this.storage) {
            Visualizer.text('Storage', { x: boxX, y: y, roomName: this.room.name });
            Visualizer.barGraph(_.sum(this.storage.store) / this.storage.storeCapacity, { x: boxX + 4, y: y, roomName: this.room.name }, 5);
            y += 1;
        }
        if (this.terminal) {
            Visualizer.text('Terminal', { x: boxX, y: y, roomName: this.room.name });
            Visualizer.barGraph(_.sum(this.terminal.store) / this.terminal.storeCapacity, { x: boxX + 4, y: y, roomName: this.room.name }, 5);
            y += 1;
        }
        return { x: x, y: y + .25 };
    }
};
CommandCenter.settings = {
    linksTransmitAt: LINK_CAPACITY - 100,
    refillTowersBelow: 750,
};
CommandCenter = CommandCenter_1 = __decorate([
    profile
], CommandCenter);

let UpgradingOverlord = class UpgradingOverlord extends Overlord {
    constructor(upgradeSite, priority = OverlordPriority.upgrading.upgrade) {
        super(upgradeSite, 'upgrade', priority);
        this.upgradeSite = upgradeSite;
        this.upgraders = this.zerg(Roles.upgrader, {
            boostWishlist: [boostResources.upgrade[3]]
        });
    }
    init() {
        if (this.colony.level < 3) { // can't spawn upgraders at early levels
            return;
        }
        if (this.colony.assets[RESOURCE_ENERGY] > UpgradeSite.settings.storageBuffer
            || this.upgradeSite.controller.ticksToDowngrade < 500) {
            const setup = this.colony.level == 8 ? Setups.upgraders.rcl8 : Setups.upgraders.default;
            if (this.colony.level == 8) {
                this.wishlist(1, setup);
            }
            else {
                const upgradePowerEach = setup.getBodyPotential(WORK, this.colony);
                const upgradersNeeded = Math.ceil(this.upgradeSite.upgradePowerNeeded / upgradePowerEach);
                this.wishlist(upgradersNeeded, setup);
            }
        }
    }
    handleUpgrader(upgrader) {
        if (upgrader.carry.energy > 0) {
            // Repair link
            if (this.upgradeSite.link && this.upgradeSite.link.hits < this.upgradeSite.link.hitsMax) {
                upgrader.task = Tasks.repair(this.upgradeSite.link);
                return;
            }
            // Repair container
            if (this.upgradeSite.battery && this.upgradeSite.battery.hits < this.upgradeSite.battery.hitsMax) {
                upgrader.task = Tasks.repair(this.upgradeSite.battery);
                return;
            }
            // Build construction site
            const inputSite = this.upgradeSite.findInputConstructionSite();
            if (inputSite) {
                upgrader.task = Tasks.build(inputSite);
                return;
            }
            // Sign controller if needed
            if (!this.upgradeSite.controller.signedByMe &&
                !this.upgradeSite.controller.signedByScreeps) {
                upgrader.task = Tasks.signController(this.upgradeSite.controller);
                return;
            }
            upgrader.task = Tasks.upgrade(this.upgradeSite.controller);
        }
        else {
            // Recharge from link or battery
            if (this.upgradeSite.link && this.upgradeSite.link.energy > 0) {
                upgrader.task = Tasks.withdraw(this.upgradeSite.link);
            }
            else if (this.upgradeSite.battery && this.upgradeSite.battery.energy > 0) {
                upgrader.task = Tasks.withdraw(this.upgradeSite.battery);
            }
            // Find somewhere else to recharge from
            else {
                if (this.upgradeSite.battery && this.upgradeSite.battery.targetedBy.length == 0) {
                    upgrader.task = Tasks.recharge();
                }
            }
        }
    }
    run() {
        this.autoRun(this.upgraders, upgrader => this.handleUpgrader(upgrader));
    }
};
UpgradingOverlord = __decorate([
    profile
], UpgradingOverlord);

// Upgrade site for grouping relevant components for an upgrader station
var UpgradeSite_1;
let UpgradeSite = UpgradeSite_1 = class UpgradeSite extends HiveCluster {
    constructor(colony, controller) {
        super(colony, controller, 'upgradeSite');
        this.controller = controller;
        this.memory = Mem.wrap(this.colony.memory, 'upgradeSite');
        this.upgradePowerNeeded = this.getUpgradePowerNeeded();
        // Register bettery
        $.set(this, 'battery', () => {
            let allowableContainers = _.filter(this.room.containers, container => container.pos.findInRange(FIND_SOURCES, 1).length == 0); // only count containers that aren't near sources
            return this.pos.findClosestByLimitedRange(allowableContainers, 3);
        });
        this.batteryPos = $.pos(this, 'batteryPos', () => {
            if (this.battery) {
                return this.battery.pos;
            }
            const inputSite = this.findInputConstructionSite();
            if (inputSite) {
                return inputSite.pos;
            }
            return this.calculateBatteryPos() || log.alert(`Upgrade site at ${this.pos.print}: no batteryPos!`);
        });
        if (this.batteryPos)
            this.colony.destinations.push({ pos: this.batteryPos, order: 0 });
        // Register link
        $.set(this, 'link', () => this.pos.findClosestByLimitedRange(colony.availableLinks, 3));
        this.colony.linkNetwork.claimLink(this.link);
        // // Energy per tick is sum of upgrader body parts and nearby worker body parts
        // this.energyPerTick = $.number(this, 'energyPerTick', () =>
        // 	_.sum(this.overlord.upgraders, upgrader => upgrader.getActiveBodyparts(WORK)) +
        // 	_.sum(_.filter(this.colony.getCreepsByRole(WorkerSetup.role), worker =>
        // 			  worker.pos.inRangeTo((this.link || this.battery || this).pos, 2)),
        // 		  worker => worker.getActiveBodyparts(WORK)));
        // Compute stats
        this.stats();
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'upgradeSite');
        $.refreshRoom(this);
        $.refresh(this, 'controller', 'battery', 'link');
    }
    spawnMoarOverlords() {
        // Register overlord
        this.overlord = new UpgradingOverlord(this);
    }
    findInputConstructionSite() {
        let nearbyInputSites = this.pos.findInRange(this.room.constructionSites, 4, {
            filter: (s) => s.structureType == STRUCTURE_CONTAINER ||
                s.structureType == STRUCTURE_LINK,
        });
        return _.first(nearbyInputSites);
    }
    getUpgradePowerNeeded() {
        return $.number(this, 'upgradePowerNeeded', () => {
            if (this.room.storage) { // Workers perform upgrading until storage is set up
                let amountOver = Math.max(this.colony.assets.energy - UpgradeSite_1.settings.storageBuffer, 0);
                let upgradePower = 1 + Math.floor(amountOver / UpgradeSite_1.settings.energyPerBodyUnit);
                if (amountOver > 800000) {
                    upgradePower *= 4; // double upgrade power if we have lots of surplus energy
                }
                else if (amountOver > 500000) {
                    upgradePower *= 2;
                }
                if (this.controller.level == 8) {
                    upgradePower = Math.min(upgradePower, 15); // don't go above 15 work parts at RCL 8
                }
                return upgradePower;
            }
            else {
                return 0;
            }
        });
    }
    init() {
        // Register energy requests
        if (this.link && this.link.energy < UpgradeSite_1.settings.linksRequestBelow) {
            this.colony.linkNetwork.requestReceive(this.link);
        }
        let inThreshold = this.colony.stage > ColonyStage.Larva ? 0.5 : 0.75;
        if (this.battery) {
            if (this.battery.energy < inThreshold * this.battery.storeCapacity) {
                let energyPerTick = UPGRADE_CONTROLLER_POWER * this.upgradePowerNeeded;
                this.colony.logisticsNetwork.requestInput(this.battery, { dAmountdt: energyPerTick });
            }
            if (hasMinerals(this.battery.store)) { // get rid of any minerals in the container if present
                this.colony.logisticsNetwork.requestOutputMinerals(this.battery);
            }
        }
    }
    /* Calculate where the input will be built for this site */
    calculateBatteryPos() {
        let originPos = undefined;
        if (this.colony.storage) {
            originPos = this.colony.storage.pos;
        }
        else if (this.colony.roomPlanner.storagePos) {
            originPos = this.colony.roomPlanner.storagePos;
        }
        else {
            return;
        }
        // Find all positions at range 2 from controller
        let inputLocations = [];
        for (let pos of this.pos.getPositionsAtRange(2)) {
            if (pos.isWalkable(true)) {
                inputLocations.push(pos);
            }
        }
        // Try to find locations where there is maximal standing room
        let maxNeighbors = _.max(_.map(inputLocations, pos => pos.availableNeighbors(true).length));
        inputLocations = _.filter(inputLocations, pos => pos.availableNeighbors(true).length >= maxNeighbors);
        // Return location closest to storage by path
        let inputPos = originPos.findClosestByPath(inputLocations);
        if (inputPos) {
            return inputPos;
        }
    }
    /* Build a container output at the optimal location */
    buildBatteryIfMissing() {
        if (!this.battery && !this.findInputConstructionSite()) {
            let buildHere = this.batteryPos;
            if (buildHere) {
                let result = buildHere.createConstructionSite(STRUCTURE_CONTAINER);
                if (result == OK) {
                    return;
                }
                else {
                    log.warning(`Upgrade site at ${this.pos.print}: cannot build battery! Result: ${result}`);
                }
            }
        }
    }
    stats() {
        let defaults = {
            downtime: 0,
        };
        if (!this.memory.stats)
            this.memory.stats = defaults;
        _.defaults(this.memory.stats, defaults);
        // Compute downtime
        this.memory.stats.downtime = (this.memory.stats.downtime * (CREEP_LIFE_TIME - 1) +
            (this.battery ? +this.battery.isEmpty : 0)) / CREEP_LIFE_TIME;
        Stats.log(`colonies.${this.colony.name}.upgradeSite.downtime`, this.memory.stats.downtime);
    }
    run() {
        if (Game.time % 25 == 7 && this.colony.level >= 2) {
            this.buildBatteryIfMissing();
        }
    }
    visuals() {
        // let info = [];
        // if (this.controller.level != 8) {
        // 	let progress = `${Math.floor(this.controller.progress / 1000)}K`;
        // 	let progressTotal = `${Math.floor(this.controller.progressTotal / 1000)}K`;
        // 	let percent = `${Math.floor(100 * this.controller.progress / this.controller.progressTotal)}`;
        // 	info.push(`Progress: ${progress}/${progressTotal} (${percent}%)`);
        //
        // }
        // info.push(`Downtime: ${this.memory.stats.downtime.toPercent()}`);
        // Visualizer.showInfo(info, this);
    }
};
// energyPerTick: number;
UpgradeSite.settings = {
    storageBuffer: 100000,
    energyPerBodyUnit: 25000,
    minLinkDistance: 10,
    linksRequestBelow: 200,
};
UpgradeSite = UpgradeSite_1 = __decorate([
    profile
], UpgradeSite);

// A grouping for objectives that allows colony components to have their own objectives instead of all being on Overlord
let LinkNetwork = class LinkNetwork {
    constructor(colony) {
        this.colony = colony;
        this.receive = [];
        this.transmit = [];
        this.settings = {
            linksTrasmitAt: LINK_CAPACITY - 100,
        };
    }
    refresh() {
        this.receive = [];
        this.transmit = [];
    }
    claimLink(link) {
        if (link) {
            _.remove(this.colony.availableLinks, l => l.id == link.id);
        }
    }
    requestReceive(link) {
        this.receive.push(link);
    }
    requestTransmit(link) {
        this.transmit.push(link);
    }
    /* Number of ticks until a dropoff link is available again to deposit energy to */
    getDropoffAvailability(link) {
        let dest = this.colony.commandCenter ? this.colony.commandCenter.pos : this.colony.pos;
        let usualCooldown = link.pos.getRangeTo(dest);
        if (link.energy > this.settings.linksTrasmitAt) { // Energy will be sent next time cooldown == 0
            return link.cooldown + usualCooldown;
        }
        else {
            return link.cooldown;
        }
    }
    init() {
        // for (let link of this.colony.dropoffLinks) {
        // 	if (link.energy > this.settings.linksTrasmitAt) {
        // 		this.requestTransmit(link);
        // 	}
        // }
    }
    /* Examine the link resource requests and try to efficiently (but greedily) match links that need energy in and
     * out, then send the remaining resourceOut link requests to the command center link */
    run() {
        // For each receiving link, greedily get energy from the closest transmitting link - at most 9 operations
        for (let receiveLink of this.receive) {
            let closestTransmitLink = receiveLink.pos.findClosestByRange(this.transmit);
            // If a send-receive match is found, transfer that first, then remove the pair from the link lists
            if (closestTransmitLink) {
                // Send min of (all the energy in sender link, amount of available space in receiver link)
                let amountToSend = _.min([closestTransmitLink.energy, receiveLink.energyCapacity - receiveLink.energy]);
                closestTransmitLink.transferEnergy(receiveLink, amountToSend);
                _.remove(this.transmit, link => link == closestTransmitLink);
                // _.remove(this.receive, link => link == receiveLink);
            }
        }
        // Now send all remaining transmit link requests to the command center
        if (this.colony.commandCenter && this.colony.commandCenter.link) {
            for (let transmitLink of this.transmit) {
                transmitLink.transferEnergy(this.colony.commandCenter.link);
            }
        }
    }
};
LinkNetwork = __decorate([
    profile
], LinkNetwork);

/**
 @param {PathFinder.CostMatrix} foregroundPixels - object pixels. modified for output
 @param {number} oob - value used for pixels outside image bounds
 @return {PathFinder.CostMatrix}

 the oob parameter is used so that if an object pixel is at the image boundary
 you can avoid having that reduce the pixel's value in the final output. Set
 it to a high value (e.g., 255) for this. Set oob to 0 to treat out of bounds
 as background pixels.
 */
function applyDistanceTransform(foregroundPixels, oob = 255) {
    let dist = foregroundPixels; // not a copy. We're modifying the input
    // Variables to represent the 3x3 neighborhood of a pixel.
    let UL, U, UR;
    let L, mid, R;
    let BL, B, BR;
    let x, y, value;
    for (y = 0; y < 50; ++y) {
        for (x = 0; x < 50; ++x) {
            if (foregroundPixels.get(x, y) !== 0) {
                UL = dist.get(x - 1, y - 1);
                U = dist.get(x, y - 1);
                UR = dist.get(x + 1, y - 1);
                L = dist.get(x - 1, y);
                if (y == 0) {
                    UL = oob;
                    U = oob;
                    UR = oob;
                }
                if (x == 0) {
                    UL = oob;
                    L = oob;
                }
                if (x == 49) {
                    UR = oob;
                }
                dist.set(x, y, Math.min(UL, U, UR, L, 254) + 1);
            }
        }
    }
    for (y = 49; y >= 0; --y) {
        for (x = 49; x >= 0; --x) {
            mid = dist.get(x, y);
            R = dist.get(x + 1, y);
            BL = dist.get(x - 1, y + 1);
            B = dist.get(x, y + 1);
            BR = dist.get(x + 1, y + 1);
            if (y == 49) {
                BL = oob;
                B = oob;
                BR = oob;
            }
            if (x == 49) {
                R = oob;
                BR = oob;
            }
            if (x == 0) {
                BL = oob;
            }
            value = Math.min(mid, R + 1, BL + 1, B + 1, BR + 1);
            dist.set(x, y, value);
        }
    }
    return dist;
}
// Compute a cost matrix for walkable pixels in a room
function walkablePixelsForRoom(roomName) {
    var costMatrix = new PathFinder.CostMatrix();
    const terrain = Game.map.getRoomTerrain(roomName);
    for (var y = 0; y < 50; ++y) {
        for (var x = 0; x < 50; ++x) {
            if (terrain.get(x, y) != TERRAIN_MASK_WALL) {
                costMatrix.set(x, y, 1);
            }
        }
    }
    return costMatrix;
}
function wallOrAdjacentToExit(x, y, roomName) {
    const terrain = Game.map.getRoomTerrain(roomName);
    if (1 < x && x < 48 && 1 < y && y < 48) {
        return terrain.get(x, y) == TERRAIN_MASK_WALL;
    }
    if (0 == x || 0 == y || 49 == x || 49 == y) {
        return true;
    }
    if (terrain.get(x, y) == TERRAIN_MASK_WALL) {
        return true;
    }
    // If we've reached here then position is a walkable neighbor to an exit tile
    let A, B, C;
    if (x == 1) {
        A = terrain.get(0, y - 1);
        B = terrain.get(0, y);
        C = terrain.get(0, y + 1);
    }
    else if (x == 48) {
        A = terrain.get(49, y - 1);
        B = terrain.get(49, y);
        C = terrain.get(49, y + 1);
    }
    if (y == 1) {
        A = terrain.get(x - 1, 0);
        B = terrain.get(x, 0);
        C = terrain.get(x + 1, 0);
    }
    else if (y == 48) {
        A = terrain.get(x - 1, 49);
        B = terrain.get(x, 49);
        C = terrain.get(x + 1, 49);
    }
    return !(A == TERRAIN_MASK_WALL && B == TERRAIN_MASK_WALL && C == TERRAIN_MASK_WALL);
}
// Compute positions where you can build movement-blocking structures in a room
function blockablePixelsForRoom(roomName) {
    var costMatrix = new PathFinder.CostMatrix();
    for (var y = 0; y < 50; ++y) {
        for (var x = 0; x < 50; ++x) {
            if (!wallOrAdjacentToExit(x, y, roomName)) {
                costMatrix.set(x, y, 1);
            }
        }
    }
    return costMatrix;
}
// Visualize a given costMatrix globally
function displayCostMatrix(costMatrix, color = '#ff0000') {
    var vis = new RoomVisual();
    var max = 1;
    for (var y = 0; y < 50; ++y) {
        for (var x = 0; x < 50; ++x) {
            max = Math.max(max, costMatrix.get(x, y));
        }
    }
    for (var y = 0; y < 50; ++y) {
        for (var x = 0; x < 50; ++x) {
            var value = costMatrix.get(x, y);
            if (value > 0) {
                vis.circle(x, y, { radius: costMatrix.get(x, y) / max / 2, fill: color });
            }
        }
    }
}
function testDistanceTransform(roomName = 'sim') {
    let dt = applyDistanceTransform(walkablePixelsForRoom(roomName));
    displayCostMatrix(dt);
}
function distanceTransform(roomName) {
    return applyDistanceTransform(walkablePixelsForRoom(roomName));
}

const MAX_SAMPLE = 10;
const MAX_TOTAL_PATH_LENGTH = 25 * 3;
let BasePlanner = class BasePlanner {
    static getBunkerLocation(room, visualize = true) {
        let colony = Overmind.colonies[room.name];
        if (colony && colony.bunker && colony.bunker.anchor) {
            return colony.bunker.anchor;
        }
        let allowableLocations = this.getAllowableBunkerLocations(room, visualize);
        if (allowableLocations.length > MAX_SAMPLE) {
            allowableLocations = _.sample(allowableLocations, MAX_SAMPLE);
        }
        let minimizePathLengthTo = _.map(_.compact([...room.sources, room.controller]), obj => obj.pos);
        let totalPathLength = function (anchor) {
            let totalDistance = 0;
            for (let pos of minimizePathLengthTo) {
                let ret = Pathing.findShortestPath(anchor, pos, { ignoreStructures: true });
                if (!ret.incomplete) {
                    totalDistance += ret.path.length;
                }
                else {
                    totalDistance += Infinity;
                }
            }
            return totalDistance;
        };
        let bestAnchor = minBy(allowableLocations, pos => totalPathLength(pos));
        if (bestAnchor && totalPathLength(bestAnchor) <= MAX_TOTAL_PATH_LENGTH) {
            return bestAnchor;
        }
    }
    static getAllowableBunkerLocations(room, visualize = true) {
        let allowableLocations = this.getNonIntersectingBunkerLocations(room.name, visualize);
        if (allowableLocations.length > MAX_SAMPLE) {
            allowableLocations = _.sample(allowableLocations, MAX_SAMPLE);
        }
        // Filter intersection with controller
        if (!room.controller)
            return [];
        allowableLocations = _.filter(allowableLocations, anchor => !this.bunkerIntersectsWith(anchor, room.controller.pos, 3));
        // Filter intersection with miningSites
        let sitesAndMineral = _.map(_.compact([...room.sources, room.mineral]), obj => obj.pos);
        allowableLocations = _.filter(allowableLocations, anchor => !_.any(sitesAndMineral, pos => this.bunkerIntersectsWith(anchor, pos, 1)));
        if (visualize) {
            let vis = room.visual;
            for (let pos of allowableLocations) {
                vis.circle(pos.x, pos.y, { fill: 'purple' });
            }
        }
        return allowableLocations;
    }
    static getNonIntersectingBunkerLocations(roomName, visualize = true) {
        let dt = distanceTransform(roomName);
        let coords = [];
        let x, y, value;
        for (y of _.range(BUNKER_RADIUS + 2, 50 - (BUNKER_RADIUS + 2))) {
            for (x of _.range(BUNKER_RADIUS + 2, 50 - (BUNKER_RADIUS + 2))) {
                if (dt.get(x, y) >= BUNKER_RADIUS + 1) {
                    // If it fits, I sits
                    coords.push({ x, y });
                }
                else if (dt.get(x, y) >= (BUNKER_RADIUS - 1) && !this.terrainIntersectsWithBunker({ x, y }, dt)) {
                    // If it might not fits, check that it fits before I sits
                    coords.push({ x, y });
                }
            }
        }
        if (visualize) {
            let vis = new RoomVisual(roomName);
            for (let coord of coords) {
                vis.text(dt.get(coord.x, coord.y).toString(), coord.x, coord.y);
            }
        }
        return _.map(coords, coord => new RoomPosition(coord.x, coord.y, roomName));
    }
    static terrainIntersectsWithBunker(anchor, distanceMatrix) {
        let dx = anchor.x - bunkerLayout.data.anchor.x;
        let dy = anchor.y - bunkerLayout.data.anchor.y;
        let bunkerCoordsAtAnchor = _.map(allBunkerCoords[8], function (coord) {
            return { x: coord.x + dx, y: coord.y + dy };
        });
        return _.any(bunkerCoordsAtAnchor, coord => distanceMatrix.get(coord.x, coord.y) == 0);
    }
    static bunkerIntersectsWith(anchor, obstacle, padding = 1) {
        let dx = bunkerLayout.data.anchor.x - anchor.x;
        let dy = bunkerLayout.data.anchor.y - anchor.y;
        let x, y;
        for (x of _.range(obstacle.x + dx - padding, obstacle.x + dx + padding + 1)) {
            for (y of _.range(obstacle.y + dy - padding, obstacle.y + dy + padding + 1)) {
                if (bunkerCoordLookup[8][coordName({ x, y })]) {
                    return true;
                }
            }
        }
        return false;
    }
};
BasePlanner = __decorate([
    profile
], BasePlanner);

const EXPANSION_EVALUATION_FREQ = 500;
const MIN_EXPANSION_DISTANCE = 2;
let ExpansionPlanner = class ExpansionPlanner {
    static refreshExpansionData(colony) {
        // This only gets run once per colony
        if (_.keys(colony.memory.expansionData.possibleExpansions).length == 0
            || Game.time > colony.memory.expansionData.expiration) {
            // Generate a list of rooms which can possibly be settled in
            let nearbyRooms = Cartographer.recursiveRoomSearch(colony.room.name, 5);
            let possibleExpansions = [];
            for (let depth in nearbyRooms) {
                if (parseInt(depth) <= MIN_EXPANSION_DISTANCE)
                    continue;
                possibleExpansions = possibleExpansions.concat(nearbyRooms[depth]);
            }
            for (let roomName of possibleExpansions) {
                if (Cartographer.roomType(roomName) == ROOMTYPE_CONTROLLER) {
                    colony.memory.expansionData.possibleExpansions[roomName] = true;
                }
            }
        }
        // This gets run whenever function is called
        for (let roomName in colony.memory.expansionData.possibleExpansions) {
            if (colony.memory.expansionData.possibleExpansions[roomName] == true) {
                if (Memory.rooms[roomName]) {
                    let expansionData = Memory.rooms[roomName].expansionData;
                    if (expansionData == false) {
                        colony.memory.expansionData.possibleExpansions[roomName] = false;
                    }
                    else if (expansionData && expansionData.score) {
                        colony.memory.expansionData.possibleExpansions[roomName] = expansionData.score;
                    }
                }
            }
        }
    }
    // Compute the total score for a room
    static computeExpansionData(room, verbose = false) {
        if (verbose)
            log.info(`Computing score for ${room.print}...`);
        if (!room.controller) {
            room.memory.expansionData = false;
            return false;
        }
        // compute possible outposts (includes host room)
        let possibleOutposts = Cartographer.findRoomsInRange(room.name, 2);
        // find source positions
        let outpostSourcePositions = {};
        for (let roomName of possibleOutposts) {
            if (Cartographer.roomType(roomName) == ROOMTYPE_ALLEY)
                continue;
            let roomMemory = Memory.rooms[roomName];
            if (!roomMemory || !roomMemory.src) {
                if (verbose)
                    log.info(`No memory of neighbor: ${roomName}. Aborting score calculation!`);
                return false;
            }
            outpostSourcePositions[roomName] = _.map(roomMemory.src, obj => derefCoords(obj.c, roomName));
        }
        // compute a possible bunker position
        let bunkerLocation = BasePlanner.getBunkerLocation(room, false);
        if (!bunkerLocation) {
            room.memory.expansionData = false;
            log.info(`Room ${room.name} is uninhabitable because a bunker can't be built here!`);
            return false;
        }
        // evaluate energy contribution and compute outpost scores
        if (verbose)
            log.info(`Origin: ${bunkerLocation.print}`);
        let outpostScores = {};
        for (let roomName in outpostSourcePositions) {
            if (verbose)
                log.info(`Analyzing neighbor ${roomName}`);
            let sourcePositions = outpostSourcePositions[roomName];
            let valid = true;
            let roomType = Cartographer.roomType(roomName);
            let energyPerSource = SOURCE_ENERGY_CAPACITY;
            if (roomType == ROOMTYPE_SOURCEKEEPER) {
                energyPerSource = 0.6 * SOURCE_ENERGY_KEEPER_CAPACITY; // don't favor SK rooms too heavily -- more CPU
            }
            else if (roomType == ROOMTYPE_CORE) {
                energyPerSource = SOURCE_ENERGY_KEEPER_CAPACITY;
            }
            let roomScore = 0;
            for (let position of sourcePositions) {
                let msg = verbose ? `Computing distance from ${bunkerLocation.print} to ${position.print}... ` : '';
                let ret = Pathing.findShortestPath(bunkerLocation, position, { ignoreStructures: true, allowHostile: true });
                if (ret.incomplete || ret.path.length > Colony.settings.maxSourceDistance) {
                    if (verbose)
                        log.info(msg + 'incomplete path!');
                    valid = false;
                    break;
                }
                if (verbose)
                    log.info(msg + ret.path.length);
                let offset = 25; // prevents over-sensitivity to very close sources
                roomScore += energyPerSource / (ret.path.length + offset);
            }
            if (valid) {
                outpostScores[roomName] = Math.floor(roomScore);
            }
        }
        // Compute the total score of the room as the maximum energy score of max number of sources harvestable
        let totalScore = 0;
        let sourceCount = 0;
        let roomsByScore = _.sortBy(_.keys(outpostScores), roomName => -1 * outpostScores[roomName]);
        for (let roomName of roomsByScore) {
            if (sourceCount > Colony.settings.remoteSourcesByLevel[8])
                break;
            let factor = roomName == room.name ? 2 : 1; // weight owned room scores more heavily
            totalScore += outpostScores[roomName];
            sourceCount += outpostSourcePositions[roomName].length;
        }
        totalScore = Math.floor(totalScore);
        if (verbose)
            log.info(`Score: ${totalScore}`);
        if (!room.memory.expansionData || totalScore > room.memory.expansionData.score) {
            room.memory.expansionData = {
                score: totalScore,
                bunkerAnchor: bunkerLocation.coordName,
                outposts: outpostScores,
            };
        }
        return true;
    }
};
ExpansionPlanner = __decorate([
    profile
], ExpansionPlanner);

// Room intel - provides information related to room structure and occupation
const RECACHE_TIME = 2500;
const OWNED_RECACHE_TIME = 1000;
const ROOM_CREEP_HISTORY_TICKS = 25;
const SCORE_RECALC_PROB = 0.05;
const FALSE_SCORE_RECALC_PROB = 0.01;
const RoomIntelMemoryDefaults = {};
let RoomIntel = class RoomIntel {
    /* Records all info for permanent room objects, e.g. sources, controllers, etc. */
    static recordPermanentObjects(room) {
        let savedSources = [];
        for (let source of room.sources) {
            let container = source.pos.findClosestByLimitedRange(room.containers, 2);
            savedSources.push({
                c: source.pos.coordName,
                contnr: container ? container.pos.coordName : undefined
            });
        }
        room.memory.src = savedSources;
        room.memory.ctrl = room.controller ? {
            c: room.controller.pos.coordName,
            level: room.controller.level,
            owner: room.controller.owner ? room.controller.owner.username : undefined,
            res: room.controller.reservation,
            SM: room.controller.safeMode,
            SMavail: room.controller.safeModeAvailable,
            SMcd: room.controller.safeModeCooldown,
            prog: room.controller.progress,
            progTot: room.controller.progressTotal
        } : undefined;
        room.memory.mnrl = room.mineral ? {
            c: room.mineral.pos.coordName,
            density: room.mineral.density,
            mineralType: room.mineral.mineralType
        } : undefined;
        room.memory.SKlairs = _.map(room.keeperLairs, lair => {
            return { c: lair.pos.coordName };
        });
        if (room.controller && room.controller.owner) {
            room.memory.importantStructs = {
                towers: _.map(room.towers, t => t.pos.coordName),
                spawns: _.map(room.spawns, s => s.pos.coordName),
                storage: room.storage ? room.storage.pos.coordName : undefined,
                terminal: room.terminal ? room.terminal.pos.coordName : undefined,
                walls: _.map(room.walls, w => w.pos.coordName),
                ramparts: _.map(room.ramparts, r => r.pos.coordName),
            };
        }
        else {
            room.memory.importantStructs = undefined;
        }
        room.memory.tick = Game.time;
    }
    // Update time-sensitive reservation and safemode info
    static recordControllerInfo(controller) {
        if (controller.room.memory.ctrl) {
            controller.room.memory.ctrl.res = controller.reservation;
            controller.room.memory.ctrl.SM = controller.safeMode;
            controller.room.memory.ctrl.SMcd = controller.safeModeCooldown;
        }
    }
    static recomputeScoreIfNecessary(room) {
        if (room.memory.expansionData == false) { // room is uninhabitable or owned
            if (Math.random() < FALSE_SCORE_RECALC_PROB) {
                // false scores get evaluated very occasionally
                return ExpansionPlanner.computeExpansionData(room);
            }
        }
        else { // if the room is not uninhabitable
            if (!room.memory.expansionData || Math.random() < SCORE_RECALC_PROB) {
                // recompute some of the time
                return ExpansionPlanner.computeExpansionData(room);
            }
        }
        return false;
    }
    static updateInvasionData(room) {
        if (!room.memory.invasionData) {
            room.memory.invasionData = {
                harvested: 0,
                lastSeen: 0,
            };
        }
        const sources = room.sources;
        for (let source of sources) {
            if (source.ticksToRegeneration == 1) {
                room.memory.invasionData.harvested += source.energyCapacity - source.energy;
            }
        }
        if (room.invaders.length > 0) {
            room.memory.invasionData = {
                harvested: 0,
                lastSeen: Game.time,
            };
        }
    }
    static updateHarvestData(room) {
        if (!room.memory.harvest) {
            room.memory.harvest = {
                amt: 0,
                avg10k: _.sum(room.sources, s => s.energyCapacity / ENERGY_REGEN_TIME),
                avg100k: _.sum(room.sources, s => s.energyCapacity / ENERGY_REGEN_TIME),
                avg1M: _.sum(room.sources, s => s.energyCapacity / ENERGY_REGEN_TIME),
                tick: Game.time,
            };
        }
        for (let source of room.sources) { // TODO: this implicitly assumes all energy is harvested by me
            if (source.ticksToRegeneration == 1) {
                const dEnergy = source.energyCapacity - source.energy;
                const dTime = Game.time - room.memory.harvest.tick + 1; // +1 to avoid division by zero errors
                room.memory.harvest.amt += dEnergy;
                room.memory.harvest.avg10k = irregularExponentialMovingAverage(dEnergy / dTime, room.memory.harvest.avg10k, dTime, 10000);
                room.memory.harvest.avg100k = irregularExponentialMovingAverage(dEnergy / dTime, room.memory.harvest.avg100k, dTime, 100000);
                room.memory.harvest.avg1M = irregularExponentialMovingAverage(dEnergy / dTime, room.memory.harvest.avg1M, dTime, 1000000);
                room.memory.harvest.tick = Game.time;
            }
        }
    }
    static updateCasualtyData(room) {
        if (!room.memory.casualties) {
            room.memory.casualties = {
                cost: {
                    amt: 0,
                    avg10k: 0,
                    avg100k: 0,
                    avg1M: 0,
                    tick: Game.time,
                }
            };
        }
        for (let tombstone of room.tombstones) {
            if (tombstone.ticksToDecay == 1) {
                // record any casualties, which are my creeps which died prematurely
                if ((tombstone.creep.ticksToLive || 0) > 1 && tombstone.creep.owner.username == MY_USERNAME) {
                    const body = _.map(tombstone.creep.body, part => part.type);
                    const lifetime = body.includes(CLAIM) ? CREEP_CLAIM_LIFE_TIME : CREEP_LIFE_TIME;
                    const dCost = bodyCost(body) * (tombstone.creep.ticksToLive || 0) / lifetime;
                    const dTime = Game.time - room.memory.casualties.cost.tick + 1;
                    room.memory.casualties.cost.amt += dCost;
                    room.memory.casualties.cost.avg10k = irregularExponentialMovingAverage(dCost / dTime, room.memory.casualties.cost.avg10k, dTime, 10000);
                    room.memory.casualties.cost.avg100k = irregularExponentialMovingAverage(dCost / dTime, room.memory.casualties.cost.avg100k, dTime, 100000);
                    room.memory.casualties.cost.avg1M = irregularExponentialMovingAverage(dCost / dTime, room.memory.casualties.cost.avg1M, dTime, 1000000);
                    room.memory.casualties.cost.tick = Game.time;
                }
            }
        }
    }
    // Get the pos a creep was in on the previous tick
    static getPreviousPos(creep) {
        if (creep.room.memory.prevPositions && creep.room.memory.prevPositions[creep.id]) {
            return derefRoomPosition(creep.room.memory.prevPositions[creep.id]);
        }
        else {
            return creep.pos; // no data
        }
    }
    static recordCreepPositions(room) {
        room.memory.prevPositions = {};
        for (let creep of room.find(FIND_CREEPS)) {
            room.memory.prevPositions[creep.id] = creep.pos;
        }
    }
    static recordCreepOccupancies(room) {
        if (!room.memory.creepsInRoom) {
            room.memory.creepsInRoom = {};
        }
        for (let tick in room.memory.creepsInRoom) {
            if (parseInt(tick, 10) < Game.time - ROOM_CREEP_HISTORY_TICKS) {
                delete room.memory.creepsInRoom[tick];
            }
        }
        room.memory.creepsInRoom[Game.time] = _.map(room.hostiles, creep => creep.name);
    }
    static recordSafety(room) {
        if (!room.memory.safety) {
            room.memory.safety = {
                safeFor: 0,
                unsafeFor: 0,
                safety1k: 1,
                safety10k: 1,
                tick: Game.time
            };
        }
        let safety;
        if (room.dangerousHostiles.length > 0) {
            room.memory.safety.safeFor = 0;
            room.memory.safety.unsafeFor += 1;
            safety = 0;
        }
        else {
            room.memory.safety.safeFor += 1;
            room.memory.safety.unsafeFor = 0;
            safety = 1;
        }
        // Compute rolling averages
        let dTime = Game.time - room.memory.safety.tick;
        room.memory.safety.safety1k = irregularExponentialMovingAverage(safety, room.memory.safety.safety1k, dTime, 1000);
        room.memory.safety.safety10k = irregularExponentialMovingAverage(safety, room.memory.safety.safety10k, dTime, 10000);
        room.memory.safety.tick = Game.time;
    }
    static getSafetyData(roomName) {
        if (!Memory.rooms[roomName]) {
            Memory.rooms[roomName] = {};
        }
        if (!Memory.rooms[roomName].safety) {
            Memory.rooms[roomName].safety = {
                safeFor: 0,
                unsafeFor: 0,
                safety1k: 1,
                safety10k: 1,
                tick: Game.time
            };
        }
        return Memory.rooms[roomName].safety;
    }
    static isInvasionLikely(room) {
        const data = room.memory.invasionData;
        if (!data)
            return false;
        if (data.lastSeen > 20000) { // maybe room is surrounded by owned/reserved rooms and invasions aren't possible
            return false;
        }
        switch (room.sources.length) {
            case 1:
                return data.harvested > 90000;
            case 2:
                return data.harvested > 75000;
            case 3:
                return data.harvested > 65000;
            default: // shouldn't ever get here
                return false;
        }
    }
    static roomOwnedBy(roomName) {
        if (Memory.rooms[roomName] && Memory.rooms[roomName].ctrl && Memory.rooms[roomName].ctrl.owner) {
            if (Game.time - (Memory.rooms[roomName].tick || 0) < 25000) { // ownership expires after 25k ticks
                return Memory.rooms[roomName].ctrl.owner;
            }
        }
    }
    static roomReservedBy(roomName) {
        if (Memory.rooms[roomName] && Memory.rooms[roomName].ctrl && Memory.rooms[roomName].ctrl.res) {
            if (Game.time - (Memory.rooms[roomName].tick || 0) < 10000) { // reservation expires after 10k ticks
                return Memory.rooms[roomName].ctrl.res.username;
            }
        }
    }
    static roomReservationRemaining(roomName) {
        if (Memory.rooms[roomName] && Memory.rooms[roomName].ctrl && Memory.rooms[roomName].ctrl.res) {
            const reservation = Memory.rooms[roomName].ctrl.res;
            let timeSinceLastSeen = Game.time - (Memory.rooms[roomName].tick || 0);
            return reservation.ticksToEnd - timeSinceLastSeen;
        }
        return 0;
    }
    static run() {
        let alreadyComputedScore = false;
        for (let name in Game.rooms) {
            const room = Game.rooms[name];
            this.recordSafety(room);
            // Track invasion data, harvesting, and casualties for all colony rooms and outposts
            if (Overmind.colonyMap[room.name]) { // if it is an owned or outpost room
                this.updateInvasionData(room);
                this.updateHarvestData(room);
                this.updateCasualtyData(room);
            }
            // Record previous creep positions if needed (RoomIntel.run() is executed at end of each tick)
            if (room.hostiles.length > 0) {
                this.recordCreepPositions(room);
                if (room.my) {
                    this.recordCreepOccupancies(room);
                }
            }
            // Record location of permanent objects in room and recompute score as needed
            if (!room.memory.expiration || Game.time > room.memory.expiration ||
                (room.owner != this.roomOwnedBy(room.name))) {
                this.recordPermanentObjects(room);
                if (!alreadyComputedScore) {
                    alreadyComputedScore = this.recomputeScoreIfNecessary(room);
                }
                // Refresh cache
                let recacheTime = room.owner ? OWNED_RECACHE_TIME : RECACHE_TIME;
                room.memory.expiration = getCacheExpiration(recacheTime, 250);
            }
            if (room.controller && Game.time % 5 == 0) {
                this.recordControllerInfo(room.controller);
            }
        }
    }
};
RoomIntel = __decorate([
    profile
], RoomIntel);
// For debugging purposes
global.RoomIntel = RoomIntel;

// Combat Intel - provides information related to making combat-related decisions
var CombatIntel_1;
let CombatIntel = CombatIntel_1 = class CombatIntel {
    constructor(directive) {
        this.directive = directive;
    }
    get memory() {
        return Mem.wrap(this.directive.memory, 'combatIntel', {});
    }
    get room() {
        return this.directive.room;
    }
    get colony() {
        return this.directive.colony;
    }
    // Tower damage ====================================================================================================
    /* Get the tower damage at a given range */
    static singleTowerDamage(range) {
        if (range <= TOWER_OPTIMAL_RANGE) {
            return TOWER_POWER_ATTACK;
        }
        range = Math.min(range, TOWER_FALLOFF_RANGE);
        let falloff = (range - TOWER_OPTIMAL_RANGE) / (TOWER_FALLOFF_RANGE - TOWER_OPTIMAL_RANGE);
        return TOWER_POWER_ATTACK * (1 - TOWER_FALLOFF * falloff);
    }
    /* Total tower tamage from all towers in room at a given position */
    static towerDamageAtPos(pos, ignoreEnergy = false) {
        if (pos.room) {
            let expectedDamage = 0;
            for (let tower of pos.room.towers) {
                if (tower.energy > 0 || ignoreEnergy) {
                    expectedDamage += this.singleTowerDamage(pos.getRangeTo(tower));
                }
            }
            return expectedDamage;
        }
        else {
            log.warning(`CombatIntel.towerDamageAtPos: room visibility at ${pos.print}!`);
            return 0;
        }
    }
    // Cost matrix calculations
    computeCostMatrix() {
        if (this.room) {
            let matrix = new PathFinder.CostMatrix();
            let barriers = this.room.barriers;
            if (barriers.length > 0) {
                let highestHits = _.last(_.sortBy(barriers, barrier => barrier.hits)).hits;
                for (let barrier of barriers) {
                    matrix.set(barrier.pos.x, barrier.pos.y, Math.ceil(barrier.hits * 10 / highestHits) * 10);
                }
            }
            return matrix;
        }
    }
    // Fallback and exit calculations ==================================================================================
    findBestExit(matrix, towers, spawns) {
        if (!this.room) {
            return;
        }
        let bestExit;
        let destination = this.room.spawns[0] || this.room.storage; // enemy structure you are trying to get to
        if (!destination) {
            return;
        }
        let ret = Pathing.findPath(this.colony.pos, destination.pos, { range: 1 });
        if (!ret.incomplete) {
            bestExit = _.find(ret.path, p => p.roomName == this.room.name);
        }
        // Figure out possible exits to go from enemy room back to colony in a reasonable amount of time
        let maxRoomDistance = 8;
        let allowedExits = {};
        if (!bestExit) {
            let exitData = Game.map.describeExits(this.room.name);
            for (let direction in exitData) {
                let roomName = exitData[direction];
                let allowedRooms = Pathing.findRoute(this.colony.name, roomName);
                if (allowedRooms && Object.keys(allowedRooms).length <= maxRoomDistance) {
                    allowedExits[direction] = true;
                }
            }
            if (_.keys(allowedExits).length == 0) {
                return;
            }
        }
        // TODO
        let exitPositions = [];
        const terrain = Game.map.getRoomTerrain(this.room.name);
        for (let x = 0; x < 50; x += 49) {
            for (let y = 0; y < 50; y++) {
                if (x !== 0 && y !== 0 && x !== 49 && y !== 49) {
                    continue;
                }
                if (terrain.get(x, y) === TERRAIN_MASK_WALL) {
                    continue;
                }
                matrix.set(x, y, 0xff);
                if (bestExit) {
                    continue;
                }
                if (allowedExits['1'] && y === 0) {
                    exitPositions.push(new RoomPosition(x, y, this.room.name));
                }
                else if (allowedExits['3'] && x === 49) {
                    exitPositions.push(new RoomPosition(x, y, this.room.name));
                }
                else if (allowedExits['5'] && y === 49) {
                    exitPositions.push(new RoomPosition(x, y, this.room.name));
                }
                else if (allowedExits['7'] && x === 0) {
                    exitPositions.push(new RoomPosition(x, y, this.room.name));
                }
            }
        }
        if (!bestExit) {
            bestExit = _(exitPositions)
                .sortBy((p) => -_.sum(towers, (t) => p.getRangeTo(t)))
                .head();
        }
        matrix.set(bestExit.x, bestExit.y, 1);
        return bestExit;
    }
    // static findBestSiegeExit(roomName: string, matrix?: CostMatrix): RoomPosition | undefined  {
    // 	let edgeCoords: [number, number][] = [];
    // 	for (let x = 0; x < 50; x += 49) {
    // 		for (let y = 0; y < 50; y++) {
    // 			edgeCoords.push([x,y])
    // 		}
    // 	}
    // 	for (let x = 0; x < 50; x++) {
    // 		for (let y = 0; y < 50; y += 49) {
    // 			edgeCoords.push([x,y])
    // 		}
    // 	}
    //
    // 	const room = Game.rooms[roomName];
    // 	let siegeTarget = CombatTargeting.findBestStructureTarget()
    // }
    /* Simple routine to find an assembly point outside of the target room */
    findSimpleSiegeFallback() {
        let ret = Pathing.findPath(this.colony.pos, this.directive.pos, { range: 23 });
        if (ret.incomplete) {
            log.warning(`Incomplete path while finding fallback! Destination: ${this.directive.pos.print}`);
        }
        let firstPosInRoom = _.find(ret.path, pos => pos.roomName == this.directive.pos.roomName);
        if (firstPosInRoom) {
            return CombatIntel_1.getFallbackFrom(firstPosInRoom);
        }
        else {
            return CombatIntel_1.getFallbackFrom(this.directive.pos);
        }
    }
    /* Finds a location for a swarm to assemble outside of the target room */
    findSwarmAssemblyPoint(clearance, swarmIndex = 0) {
        let simpleFallback = this.findSimpleSiegeFallback();
        let startPos = Pathing.findPathablePosition(simpleFallback.roomName, clearance);
        let ret = Pathing.findSwarmPath(startPos, this.directive.pos, clearance.width, clearance.height, { ignoreCreeps: true });
        let path = ret.path.reverse();
        let acceptablePositions = _.filter(path, pos => pos.roomName == simpleFallback.roomName &&
            pos.rangeToEdge > 1);
        let swarmSize = Math.max(clearance.width, clearance.height);
        let posIndex = (swarmSize + 1) * swarmIndex;
        return acceptablePositions[posIndex] || acceptablePositions[0] || simpleFallback;
    }
    /* Fallback is a location on the other side of the nearest exit the directive is placed at */
    static getFallbackFrom(pos, fallbackDistance = 2) {
        let { x, y, roomName } = pos;
        let rangesToExit = [[x, 'left'], [49 - x, 'right'], [y, 'top'], [49 - y, 'bottom']];
        let [range, direction] = _.first(_.sortBy(rangesToExit, pair => pair[0]));
        switch (direction) {
            case 'left':
                x = 49 - fallbackDistance;
                roomName = Cartographer.findRelativeRoomName(roomName, -1, 0);
                break;
            case 'right':
                x = fallbackDistance;
                roomName = Cartographer.findRelativeRoomName(roomName, 1, 0);
                break;
            case 'top':
                y = 49 - fallbackDistance;
                roomName = Cartographer.findRelativeRoomName(roomName, 0, -1);
                break;
            case 'bottom':
                y = fallbackDistance;
                roomName = Cartographer.findRelativeRoomName(roomName, 0, 1);
                break;
            default:
                log.error('Error getting fallback position!');
                break;
        }
        return new RoomPosition(x, y, roomName);
    }
    // Creep potentials ================================================================================================
    // Cache the result of a computation for a tick
    static cache(creep, key, callback) {
        if (!creep.intel)
            creep.intel = {};
        if (creep.intel[key] == undefined) {
            creep.intel[key] = callback();
        }
        return creep.intel[key];
    }
    // Heal potential of a single creep in units of effective number of parts
    static getHealPotential(creep) {
        return this.cache(creep, 'healPotential', () => _.sum(creep.body, function (part) {
            let potential = 0;
            if (part.type == HEAL) {
                if (!part.boost) {
                    potential = 1;
                }
                else if (part.boost == boostResources.heal[1]) {
                    potential = BOOSTS.heal.LO.heal;
                }
                else if (part.boost == boostResources.heal[2]) {
                    potential = BOOSTS.heal.LHO2.heal;
                }
                else if (part.boost == boostResources.heal[3]) {
                    potential = BOOSTS.heal.XLHO2.heal;
                }
            }
            return potential * part.hits / 100;
        }));
    }
    static getHealAmount(creep) {
        return HEAL_POWER * this.getHealPotential(toCreep(creep));
    }
    static getRangedHealAmount(creep) {
        return RANGED_HEAL_POWER * this.getHealPotential(toCreep(creep));
    }
    // If a creep appears to primarily be a healer
    static isHealer(zerg) {
        const creep = toCreep(zerg);
        const healParts = _.filter(zerg.body, part => part.type == HEAL).length;
        const attackParts = _.filter(zerg.body, part => part.type == ATTACK).length;
        const rangedAttackParts = _.filter(zerg.body, part => part.type == RANGED_ATTACK).length;
        return healParts > attackParts + rangedAttackParts;
    }
    // Attack potential of a single creep in units of effective number of parts
    static getAttackPotential(creep) {
        return this.cache(creep, 'attackPotential', () => _.sum(creep.body, function (part) {
            let potential = 0;
            if (part.type == ATTACK) {
                if (!part.boost) {
                    potential = 1;
                }
                else if (part.boost == boostResources.attack[1]) {
                    potential = BOOSTS.attack.UH.attack;
                }
                else if (part.boost == boostResources.attack[2]) {
                    potential = BOOSTS.attack.UH2O.attack;
                }
                else if (part.boost == boostResources.attack[3]) {
                    potential = BOOSTS.attack.XUH2O.attack;
                }
            }
            return potential * part.hits / 100;
        }));
    }
    static getAttackDamage(creep) {
        return ATTACK_POWER * this.getAttackPotential(toCreep(creep));
    }
    // Ranged attack potential of a single creep in units of effective number of parts
    static getRangedAttackPotential(creep) {
        return this.cache(creep, 'rangedAttackPotential', () => _.sum(creep.body, function (part) {
            let potential = 0;
            if (part.type == RANGED_ATTACK) {
                if (!part.boost) {
                    potential = 1;
                }
                else if (part.boost == boostResources.ranged_attack[1]) {
                    potential = BOOSTS.ranged_attack.KO.rangedAttack;
                }
                else if (part.boost == boostResources.ranged_attack[2]) {
                    potential = BOOSTS.ranged_attack.KHO2.rangedAttack;
                }
                else if (part.boost == boostResources.ranged_attack[3]) {
                    potential = BOOSTS.ranged_attack.XKHO2.rangedAttack;
                }
            }
            return potential * part.hits / 100;
        }));
    }
    static getRangedAttackDamage(creep) {
        return RANGED_ATTACK_POWER * this.getRangedAttackPotential(toCreep(creep));
    }
    // Attack potential of a single creep in units of effective number of parts
    static getDismantlePotential(creep) {
        return this.cache(creep, 'dismantlePotential', () => _.sum(creep.body, function (part) {
            let potential = 0;
            if (part.type == WORK) {
                if (!part.boost) {
                    potential = 1;
                }
                else if (part.boost == boostResources.dismantle[1]) {
                    potential = BOOSTS.work.ZH.dismantle;
                }
                else if (part.boost == boostResources.dismantle[2]) {
                    potential = BOOSTS.work.ZH2O.dismantle;
                }
                else if (part.boost == boostResources.dismantle[3]) {
                    potential = BOOSTS.work.XZH2O.dismantle;
                }
            }
            return potential * part.hits / 100;
        }));
    }
    static getDismantleDamage(creep) {
        return DISMANTLE_POWER * this.getDismantlePotential(toCreep(creep));
    }
    // Minimum damage multiplier a creep has
    static minimumDamageTakenMultiplier(creep) {
        return this.cache(creep, 'minDamageMultiplier', () => _.min(_.map(creep.body, function (part) {
            if (part.type == TOUGH && part.hits > 0) {
                if (part.boost == boostResources.tough[1]) {
                    return BOOSTS.tough.GO.damage;
                }
                else if (part.boost == boostResources.tough[2]) {
                    return BOOSTS.tough.GHO2.damage;
                }
                else if (part.boost == boostResources.tough[3]) {
                    return BOOSTS.tough.XGHO2.damage;
                }
            }
            return 1;
        })));
    }
    static minimumDamageMultiplierForGroup(creeps) {
        return _.min(_.map(creeps, creep => this.minimumDamageTakenMultiplier(creep)));
    }
    static getMassAttackDamageTo(attacker, target) {
        if (isStructure(target) && (!isOwnedStructure(target) || target.my)) {
            return 0;
        }
        let range = attacker.pos.getRangeTo(target.pos);
        let rangedMassAttackPower = 0;
        if (range <= 1) {
            rangedMassAttackPower = 10;
        }
        else if (range == 2) {
            rangedMassAttackPower = 4;
        }
        else if (range == 3) {
            rangedMassAttackPower = 1;
        }
        return rangedMassAttackPower * this.getRangedAttackPotential(isZerg(attacker) ? attacker.creep : attacker);
    }
    // Total damage to enemy creeps done by attacker.rangedMassAttack()
    static getMassAttackDamage(attacker, targets = attacker.room.hostiles, checkRampart = true) {
        let hostiles = attacker.pos.findInRange(targets, 3);
        return _.sum(hostiles, function (hostile) {
            if (checkRampart && hostile.pos.lookForStructure(STRUCTURE_RAMPART)) {
                return 0; // Creep inside rampart
            }
            else {
                return CombatIntel_1.getMassAttackDamageTo(attacker, hostile);
            }
        });
    }
    static rating(creep) {
        const c = toCreep(creep);
        return this.cache(c, 'rating', () => {
            let rating = this.getRangedAttackPotential(c) + this.getAttackPotential(c) / 2;
            let healMultiplier = 1 / this.minimumDamageTakenMultiplier(c);
            rating += healMultiplier * this.getHealPotential(c);
            return rating;
        });
    }
    // Group creep calculations ========================================================================================
    // Maximum damage that a group of creeps can dish out (doesn't count for simultaneity restrictions)
    static maxDamageByCreeps(creeps) {
        return _.sum(creeps, creep => ATTACK_POWER * this.getAttackPotential(creep) +
            RANGED_ATTACK_POWER * this.getRangedAttackPotential(creep));
    }
    // Maximum healing that a group of creeps can dish out (doesn't count for simultaneity restrictions)
    static maxHealingByCreeps(creeps) {
        return _.sum(creeps, creep => this.getHealAmount(creep));
    }
    // Total attack/rangedAttack/heal potentials for a group of creeps
    static getCombatPotentials(creeps) {
        let attack = _.sum(creeps, creep => this.getAttackPotential(creep));
        let rangedAttack = _.sum(creeps, creep => this.getRangedAttackPotential(creep));
        let heal = _.sum(creeps, creep => this.getHealPotential(creep));
        return { attack, rangedAttack, heal };
    }
    // Maximum damage that is dealable at a given position by enemy forces
    static maxDamageAtPos(pos) {
        if (!pos.room) {
            return 0;
        }
        let hostilesInMeleeRange = _.filter(pos.room.dangerousHostiles, creep => pos.getRangeTo(creep) <= 1);
        let meleeDamage = _.sum(hostilesInMeleeRange, hostile => this.getAttackDamage(hostile));
        let hostilesInRange = _.filter(pos.room.dangerousHostiles, creep => pos.getRangeTo(creep) <= 3);
        let rangedDamage = _.sum(hostilesInRange, hostile => this.getRangedAttackDamage(hostile));
        let totalDamage = meleeDamage + rangedDamage;
        if (!pos.room.my) {
            totalDamage += this.towerDamageAtPos(pos) || 0;
        }
        return totalDamage;
    }
    // Heal potential of self and possible healer neighbors
    static maxHostileHealingTo(creep) {
        return this.cache(creep, 'maxHostileHealing', () => {
            let selfHealing = this.getHealAmount(creep);
            let neighbors = _.filter(creep.room.hostiles, hostile => hostile.pos.isNearTo(creep));
            let neighborHealing = HEAL_POWER * _.sum(neighbors, neighbor => this.getHealPotential(neighbor));
            let rangedHealers = _.filter(creep.room.hostiles, hostile => hostile.pos.getRangeTo(creep) <= 3 &&
                !neighbors.includes(hostile));
            let rangedHealing = RANGED_HEAL_POWER * _.sum(rangedHealers, healer => this.getHealPotential(healer));
            return selfHealing + neighborHealing + rangedHealing;
        });
    }
    // Heal potential of self and possible healer neighbors
    static maxFriendlyHealingTo(friendly) {
        const creep = toCreep(friendly);
        return this.cache(creep, 'maxFriendlyHealing', () => {
            let selfHealing = this.getHealAmount(creep);
            let neighbors = _.filter(creep.room.creeps, hostile => hostile.pos.isNearTo(creep));
            let neighborHealing = HEAL_POWER * _.sum(neighbors, neighbor => this.getHealPotential(neighbor));
            let rangedHealers = _.filter(creep.room.creeps, hostile => hostile.pos.getRangeTo(creep) <= 3 &&
                !neighbors.includes(hostile));
            let rangedHealing = RANGED_HEAL_POWER * _.sum(rangedHealers, healer => this.getHealPotential(healer));
            return selfHealing + neighborHealing + rangedHealing;
        });
    }
    // Determine the predicted damage amount of a certain type of attack. Can specify if you should use predicted or
    // current hits amount and whether to include predicted healing. Does not update predicted hits.
    static predictedDamageAmount(attacker, target, attackType, useHitsPredicted = true) {
        // Compute initial (gross) damage amount
        let grossDamage;
        if (attackType == 'attack') {
            grossDamage = this.getAttackDamage(attacker);
        }
        else if (attackType == 'rangedAttack') {
            grossDamage = this.getRangedAttackDamage(attacker);
        }
        else { // rangedMassAttack; not currently used
            grossDamage = this.getMassAttackDamageTo(attacker, target);
        }
        // Adjust for remaining tough parts
        let toughHits;
        if (useHitsPredicted) {
            if (target.hitsPredicted == undefined)
                target.hitsPredicted = target.hits;
            let nonToughHits = _.sum(target.body, part => part.type == TOUGH ? 0 : part.hits);
            toughHits = Math.min(target.hitsPredicted - nonToughHits, 0); // predicted amount of TOUGH
        }
        else {
            toughHits = 100 * target.getActiveBodyparts(TOUGH);
        }
        let damageMultiplier = this.minimumDamageTakenMultiplier(target); // assumes only 1 tier of boosts
        if (grossDamage * damageMultiplier < toughHits) { // if you can't eat through armor
            return grossDamage * damageMultiplier;
        }
        else { // if you break tough shield
            grossDamage -= toughHits / damageMultiplier;
            return toughHits + grossDamage;
        }
    }
    // Creep position calculations =====================================================================================
    // // Distance from a given creep to the nearest rampart or wall; Infinity if no barriers in room
    // static distanceToBarrier(creep: Creep): number {
    //
    // }
    static isApproaching(approacher, toPos) {
        let previousPos = RoomIntel.getPreviousPos(approacher);
        let previousRange = toPos.getRangeTo(previousPos);
        let currentRange = toPos.getRangeTo(approacher.pos);
        return currentRange < previousRange;
    }
    static isRetreating(retreater, fromPos) {
        let previousPos = RoomIntel.getPreviousPos(retreater);
        let previousRange = fromPos.getRangeTo(previousPos);
        let currentRange = fromPos.getRangeTo(retreater.pos);
        return currentRange > previousRange;
    }
    // This method is probably expensive; use sparingly
    static isEdgeDancing(creep, reentryThreshold = 3) {
        if (!creep.room.my) {
            log.warning(`isEdgeDancing should only be called in owned rooms!`);
        }
        const creepOccupancies = creep.room.memory.creepsInRoom;
        if (creepOccupancies) {
            // Look to see if the creep has exited and re-entered the room a given number of times
            let creepInRoomTicks = [];
            for (let tick in creepOccupancies) {
                if (creepOccupancies[tick].includes(creep.name)) {
                    creepInRoomTicks.push(parseInt(tick, 10));
                }
            }
            let reentries = 1;
            if (creepInRoomTicks.length > 0) {
                for (let i of _.range(creepInRoomTicks.length - 1)) {
                    if (creepInRoomTicks[i + 1] != creepInRoomTicks[i] + 1) {
                        // There was a gap between the creep's presence in the room so it must have reentered
                        reentries++;
                    }
                }
            }
            return reentries >= reentryThreshold;
        }
        else {
            return false;
        }
    }
    static getPositionsNearEnemies(hostiles, range = 0) {
        return _.unique(_.flatten(_.map(hostiles, hostile => hostile.pos.getPositionsInRange(range, false, true))));
    }
};
CombatIntel = CombatIntel_1 = __decorate([
    profile
], CombatIntel);

let CombatTargeting = class CombatTargeting {
    /* Finds the best target within a given range that a zerg can currently attack */
    static findBestCreepTargetInRange(zerg, range, targets = zerg.room.hostiles) {
        let nearbyHostiles = _.filter(targets, c => zerg.pos.inRangeToXY(c.pos.x, c.pos.y, range));
        return maxBy(nearbyHostiles, function (hostile) {
            if (hostile.hitsPredicted == undefined)
                hostile.hitsPredicted = hostile.hits;
            if (hostile.pos.lookForStructure(STRUCTURE_RAMPART))
                return false;
            return hostile.hitsMax - hostile.hitsPredicted + CombatIntel.getHealPotential(hostile); // compute score
        });
    }
    /* Finds the best target within a given range that a zerg can currently attack */
    static findBestStructureTargetInRange(zerg, range, allowUnowned = true) {
        let nearbyStructures = _.filter(zerg.room.hostileStructures, s => zerg.pos.inRangeToXY(s.pos.x, s.pos.y, range));
        // If no owned structures to attack and not in colony room or outpost, target unowned structures
        if (allowUnowned && nearbyStructures.length == 0 && !Overmind.colonyMap[zerg.room.name]) {
            nearbyStructures = _.filter(zerg.room.structures, s => zerg.pos.inRangeToXY(s.pos.x, s.pos.y, range));
        }
        return maxBy(nearbyStructures, function (structure) {
            let score = 10 * AttackStructureScores[structure.structureType];
            if (structure.pos.lookForStructure(STRUCTURE_RAMPART))
                score *= .1;
            return score;
        });
    }
    /* Standard target-finding logic */
    static findTarget(zerg, targets = zerg.room.hostiles) {
        return maxBy(targets, function (hostile) {
            if (hostile.hitsPredicted == undefined)
                hostile.hitsPredicted = hostile.hits;
            if (hostile.pos.lookForStructure(STRUCTURE_RAMPART))
                return false;
            return hostile.hitsMax - hostile.hitsPredicted + CombatIntel.getHealPotential(hostile)
                - 10 * zerg.pos.getMultiRoomRangeTo(hostile.pos); // compute score
        });
    }
    /* Finds the best target within a given range that a zerg can currently attack */
    static findBestCreepTargetForTowers(room, targets = room.hostiles) {
        return maxBy(targets, function (hostile) {
            if (hostile.hitsPredicted == undefined)
                hostile.hitsPredicted = hostile.hits;
            if (hostile.pos.lookForStructure(STRUCTURE_RAMPART))
                return false;
            return hostile.hitsMax - hostile.hitsPredicted
                + CombatIntel.getHealPotential(hostile) + (CombatIntel.towerDamageAtPos(hostile.pos) || 0);
        });
    }
    static findClosestHostile(zerg, checkReachable = false, ignoreCreepsAtEdge = true) {
        if (zerg.room.hostiles.length > 0) {
            let targets;
            if (ignoreCreepsAtEdge) {
                targets = _.filter(zerg.room.hostiles, hostile => hostile.pos.rangeToEdge > 0);
            }
            else {
                targets = zerg.room.hostiles;
            }
            if (checkReachable) {
                let targetsByRange = _.sortBy(targets, target => zerg.pos.getRangeTo(target));
                return _.find(targetsByRange, target => Pathing.isReachable(zerg.pos, target.pos, zerg.room.barriers));
            }
            else {
                return zerg.pos.findClosestByRange(targets);
            }
        }
    }
    /* This method is expensive */
    static findClosestReachable(pos, targets) {
        let targetsByRange = _.sortBy(targets, target => pos.getRangeTo(target));
        return _.find(targetsByRange, target => Pathing.isReachable(pos, target.pos, target.room.barriers));
    }
    static findClosestHurtFriendly(healer) {
        return healer.pos.findClosestByRange(_.filter(healer.room.creeps, creep => creep.hits < creep.hitsMax));
    }
    /* Finds the best (friendly) target in range that a zerg can currently heal */
    static findBestHealingTargetInRange(healer, range = 3, friendlies = healer.room.creeps) {
        return maxBy(_.filter(friendlies, f => healer.pos.getRangeTo(f) <= range), friend => {
            if (friend.hitsPredicted == undefined)
                friend.hitsPredicted = friend.hits;
            let healScore = friend.hitsMax - friend.hitsPredicted;
            if (healer.pos.getRangeTo(friend) > 1) {
                return healScore + CombatIntel.getRangedHealAmount(healer.creep);
            }
            else {
                return healScore + CombatIntel.getHealAmount(healer.creep);
            }
        });
    }
    static findClosestPrioritizedStructure(zerg, checkReachable = false) {
        for (let structureType of AttackStructurePriorities) {
            let structures = _.filter(zerg.room.hostileStructures, s => s.structureType == structureType);
            if (structures.length == 0)
                continue;
            if (checkReachable) {
                let closestReachable = this.findClosestReachable(zerg.pos, structures);
                if (closestReachable)
                    return closestReachable;
            }
            else {
                return zerg.pos.findClosestByRange(structures);
            }
        }
    }
    static findBestStructureTarget(pos) {
        const room = Game.rooms[pos.roomName];
        // Don't accidentally destroy your own shit
        if (!room || room.my || room.reservedByMe) {
            return;
        }
        // Look for any unprotected structures
        let unprotectedRepairables = _.filter(room.repairables, s => {
            let rampart = s.pos.lookForStructure(STRUCTURE_RAMPART);
            return !rampart || rampart.hits < 10000;
        });
        let approach = _.map(unprotectedRepairables, structure => {
            return { pos: structure.pos, range: 0 };
        });
        if (room.barriers.length == 0 && unprotectedRepairables.length == 0)
            return; // if there's nothing in the room
        // Try to find a reachable unprotected structure
        if (approach.length > 0) {
            let ret = PathFinder.search(pos, approach, {
                maxRooms: 1,
                maxOps: 2000,
                roomCallback: roomName => {
                    if (roomName != room.name)
                        return false;
                    let matrix = new PathFinder.CostMatrix();
                    for (let barrier of room.barriers) {
                        matrix.set(barrier.pos.x, barrier.pos.y, 0xff);
                    }
                    return matrix;
                },
            });
            let targetPos = _.last(ret.path);
            if (!ret.incomplete && targetPos) {
                let targetStructure = _.first(_.filter(targetPos.lookFor(LOOK_STRUCTURES), s => {
                    return s.structureType != STRUCTURE_ROAD && s.structureType != STRUCTURE_CONTAINER;
                }));
                if (targetStructure) {
                    log.debug(`Found unprotected structure target @ ${targetPos.print}`);
                    return targetStructure;
                }
            }
        }
        // Determine a "siege anchor" for what you eventually want to destroy
        let targets = room.spawns;
        if (targets.length == 0)
            targets = room.repairables;
        if (targets.length == 0)
            targets = room.barriers;
        if (targets.length == 0)
            targets = room.structures;
        if (targets.length == 0)
            return;
        // Recalculate approach targets
        approach = _.map(targets, s => {
            return { pos: s.pos, range: 0 };
        });
        let maxWallHits = _.max(_.map(room.barriers, b => b.hits)) || 0;
        // Compute path with wall position costs weighted by fraction of highest wall
        let ret = PathFinder.search(pos, approach, {
            maxRooms: 1,
            plainCost: 1,
            swampCost: 2,
            roomCallback: roomName => {
                if (roomName != pos.roomName)
                    return false;
                let matrix = new PathFinder.CostMatrix();
                for (let barrier of room.barriers) {
                    let cost = 100 + Math.round((barrier.hits / maxWallHits) * 100);
                    matrix.set(barrier.pos.x, barrier.pos.y, cost);
                }
                return matrix;
            },
        });
        // Target the first non-road, non-container structure you find along the path
        for (let pos of ret.path) {
            let targetStructure = _.first(_.filter(pos.lookFor(LOOK_STRUCTURES), s => {
                return s.structureType != STRUCTURE_ROAD && s.structureType != STRUCTURE_CONTAINER;
            }));
            if (targetStructure) {
                log.debug(`Targeting structure @ ${targetStructure.pos.print}`);
                return targetStructure;
            }
        }
    }
    static findBestSwarmStructureTarget(swarm, roomName, randomness = 0) {
        const room = Game.rooms[roomName];
        // Don't accidentally destroy your own shit
        if (!room || room.my || room.reservedByMe) {
            return;
        }
        if (swarm.anchor.roomName != roomName) {
            log.warning(`Swarm is not in target room!`);
            return;
        }
        // // Look for any unprotected structures
        // let unprotectedRepairables = _.filter(room.repairables, s => {
        // 	let rampart = s.pos.lookForStructure(STRUCTURE_RAMPART);
        // 	return !rampart || rampart.hits < 10000;
        // });
        // let approach = _.map(unprotectedRepairables, structure => {
        // 	return {pos: structure.pos, range: 0};
        // }) as PathFinderGoal[];
        // if (room.barriers.length == 0 && unprotectedRepairables.length == 0) return; // if there's nothing in the room
        //
        // // Try to find a reachable unprotected structure
        // if (approach.length > 0) {
        // 	let ret = PathFinder.search(swarm.anchor, approach, {
        // 		maxRooms    : 1,
        // 		maxOps      : 2000,
        // 		roomCallback: roomName => {
        // 			if (roomName != room.name) return false;
        // 			let matrix = Pathing.getSwarmTerrainMatrix(roomName, swarm.width, swarm.height).clone();
        // 			for (let barrier of room.barriers) {
        // 				let setPositions = Pathing.getPosWindow(barrier.pos, -swarm.width, -swarm.height);
        // 				for (let pos of setPositions) {
        // 					matrix.set(pos.x, pos.y, 0xff);
        // 				}
        // 			}
        // 			return matrix;
        // 		},
        // 	});
        // 	let targetPos = _.last(ret.path);
        // 	if (!ret.incomplete && targetPos) {
        // 		let targetStructure = _.first(_.filter(targetPos.lookFor(LOOK_STRUCTURES), s => {
        // 			return s.structureType != STRUCTURE_ROAD && s.structureType != STRUCTURE_CONTAINER;
        // 		}));
        // 		if (targetStructure) {
        // 			log.debug(`Found unprotected structure target @ ${targetPos.print}`);
        // 			return targetStructure;
        // 		}
        // 	}
        // }
        // Determine a "siege anchor" for what you eventually want to destroy
        let targets = room.spawns;
        if (targets.length == 0)
            targets = room.towers;
        if (targets.length == 0)
            targets = room.repairables;
        if (targets.length == 0)
            targets = room.barriers;
        if (targets.length == 0)
            targets = room.structures;
        if (targets.length == 0)
            return;
        // Recalculate approach targets
        let approach = _.map(targets, s => {
            return { pos: s.pos, range: 0 };
        });
        let maxWallHits = _.max(_.map(room.barriers, b => b.hits)) || 0;
        // Compute path with wall position costs weighted by fraction of highest wall
        let ret = PathFinder.search(swarm.anchor, approach, {
            maxRooms: 1,
            plainCost: 1,
            swampCost: 2,
            roomCallback: roomName => {
                if (roomName != roomName)
                    return false;
                let matrix = Pathing.getSwarmTerrainMatrix(roomName, swarm.width, swarm.height).clone();
                for (let barrier of room.barriers) {
                    let randomFactor = Math.min(Math.round(randomness * Math.random()), 100);
                    let cost = 100 + Math.round((barrier.hits / maxWallHits) * 100) + randomFactor;
                    let setPositions = Pathing.getPosWindow(barrier.pos, -swarm.width, -swarm.height);
                    for (let pos of setPositions) {
                        matrix.set(pos.x, pos.y, Math.max(cost, matrix.get(pos.x, pos.y)));
                    }
                }
                return matrix;
            },
        });
        // Target the first non-road, non-container structure you find along the path or neighboring positions
        for (let pos of ret.path) {
            log.debug(`Searching path ${pos.print}...`);
            let searchPositions = Pathing.getPosWindow(pos, swarm.width, swarm.height); // not -1*width
            for (let searchPos of searchPositions) {
                let targetStructure = _.first(_.filter(searchPos.lookFor(LOOK_STRUCTURES), s => {
                    return s.structureType != STRUCTURE_ROAD && s.structureType != STRUCTURE_CONTAINER;
                }));
                if (targetStructure) {
                    log.debug(`Targeting structure @ ${targetStructure.pos.print}`);
                    return targetStructure;
                }
            }
        }
    }
};
CombatTargeting = __decorate([
    profile
], CombatTargeting);

var SporeCrawler_1;
// Hive cluster for wrapping towers
let SporeCrawler = SporeCrawler_1 = class SporeCrawler extends HiveCluster {
    constructor(colony, tower) {
        super(colony, tower, 'sporeCrawler');
        // Register structure components
        this.towers = this.colony.towers;
    }
    refresh() {
        $.refreshRoom(this);
        $.refresh(this, 'towers');
    }
    spawnMoarOverlords() {
    }
    get memory() {
        return undefined;
    }
    registerEnergyRequests() {
        // Request energy from transporters if below request threshold
        for (let tower of this.towers) {
            if (tower.energy < SporeCrawler_1.settings.requestThreshold) {
                let multiplier = tower.energy < SporeCrawler_1.settings.criticalEnergyThreshold ? 2 : 1;
                let dAmountdt = this.room.hostiles.length > 0 ? 10 : 0;
                this.colony.logisticsNetwork.requestInput(tower, { multiplier: multiplier, dAmountdt: dAmountdt });
            }
        }
    }
    init() {
        this.registerEnergyRequests();
    }
    attack(target) {
        for (let tower of this.towers) {
            let result = tower.attack(target);
            if (result == OK) {
                if (target.hitsPredicted == undefined)
                    target.hitsPredicted = target.hits;
                target.hitsPredicted -= CombatIntel.singleTowerDamage(target.pos.getRangeTo(tower));
            }
        }
    }
    // private attackNearestEnemy(prioritizeHealers = false) {
    // 	if (prioritizeHealers) {
    // 		let healers = _.filter(this.room.hostiles, creep => creep.getActiveBodyparts(HEAL) > 0);
    // 		if (healers.length > 0) {
    // 			let healer = this.pos.findClosestByRange(healers);
    // 			if (healer) {
    // 				return this.tower.attack(healer);
    // 			}
    // 		}
    // 	}
    // 	let closestHostile = this.pos.findClosestByRange(FIND_HOSTILE_CREEPS);
    // 	if (closestHostile) {
    // 		return this.tower.attack(closestHostile);
    // 	}
    // }
    // private healNearestAlly() {
    // 	var closestDamagedAlly = this.pos.findClosestByRange(FIND_MY_CREEPS, {
    // 		filter: (c: Creep) => c.hits < c.hitsMax,
    // 	});
    // 	if (closestDamagedAlly) {
    // 		return this.tower.heal(closestDamagedAlly);
    // 	}
    // }
    preventRampartDecay() {
        if (this.towers.length > 0) {
            // expensive to check all rampart hits; only run in intermediate RCL
            let dyingRamparts = _.filter(this.room.ramparts, rampart => rampart.hits < WorkerOverlord.settings.barrierHits.critical
                && this.colony.roomPlanner.barrierPlanner.barrierShouldBeHere(rampart.pos));
            if (dyingRamparts.length > 0) {
                for (let tower of this.towers) {
                    tower.repair(tower.pos.findClosestByRange(dyingRamparts));
                }
            }
        }
    }
    // private repairNearestStructure() {
    // 	var closestDamagedStructure = this.pos.findClosestByRange(FIND_STRUCTURES, {
    // 		filter: (s: Structure) => s.hits < s.hitsMax &&
    // 								  s.structureType != STRUCTURE_WALL &&
    // 								  s.structureType != STRUCTURE_RAMPART,
    // 	});
    // 	if (closestDamagedStructure) {
    // 		return this.tower.repair(closestDamagedStructure);
    // 	}
    // }
    run() {
        if (this.room.hostiles.length > 0) {
            let myDefenders = _.filter(this.room.creeps, creep => creep.getActiveBodyparts(ATTACK) > 1);
            let myRangedDefenders = _.filter(this.room.creeps, creep => creep.getActiveBodyparts(RANGED_ATTACK) > 1);
            let myCreepDamage = ATTACK_POWER * _.sum(myDefenders, creep => CombatIntel.getAttackPotential(creep)) +
                RANGED_ATTACK_POWER * _.sum(myRangedDefenders, creep => CombatIntel.getRangedAttackPotential(creep));
            const HEAL_FUDGE_FACTOR = 0.5;
            let possibleTargets = _.filter(this.room.hostiles, hostile => HEAL_FUDGE_FACTOR * CombatIntel.maxHostileHealingTo(hostile) <
                CombatIntel.towerDamageAtPos(hostile.pos) + myCreepDamage);
            // Only attack dancing targets (drain attack) which are far enough in rooms to be killed off by towers
            possibleTargets = _.filter(possibleTargets, hostile => {
                if (CombatIntel.isEdgeDancing(hostile)) {
                    let netDPS = CombatIntel.towerDamageAtPos(hostile.pos) + myCreepDamage
                        - (HEAL_FUDGE_FACTOR * CombatIntel.maxHostileHealingTo(hostile));
                    let isKillable = netDPS * hostile.pos.rangeToEdge > hostile.hits;
                    if (isKillable) {
                        return true;
                    }
                    else {
                        // Shoot if they get close enough
                        if (this.colony.bunker && this.colony.bunker.anchor &&
                            hostile.pos.getRangeTo(this.colony.bunker.anchor) <= 6 + 2) {
                            return true;
                        }
                    }
                }
                else {
                    return true;
                }
            });
            let target = CombatTargeting.findBestCreepTargetForTowers(this.room, possibleTargets);
            if (target) {
                return this.attack(target);
            }
        }
        let closestDamagedAlly = this.pos.findClosestByRange(_.filter(this.room.creeps, creep => creep.hits < creep.hitsMax));
        if (closestDamagedAlly) {
            for (let tower of this.towers) {
                tower.heal(closestDamagedAlly);
            }
            return;
        }
        // Towers build nuke response ramparts
        let nearbyNukeRamparts = _.filter(this.colony.overlords.work.nukeDefenseRamparts, rampart => this.pos.getRangeTo(rampart) <= TOWER_OPTIMAL_RANGE);
        if (nearbyNukeRamparts.length > 0) {
            for (let tower of this.towers) {
                tower.repair(nearbyNukeRamparts[0]);
            }
            return;
        }
        // Prevent rampart decay at early RCL
        this.preventRampartDecay();
    }
    visuals() {
    }
};
SporeCrawler.settings = {
    requestThreshold: 500,
    criticalEnergyThreshold: 250,
};
SporeCrawler = SporeCrawler_1 = __decorate([
    profile
], SporeCrawler);

// Road network: groups roads in a single object for more intelligent repair requests
var RoadLogistics_1;
const ROAD_CACHE_TIMEOUT = 15;
// function sortRoadsByDFS(room: Room, colony: Colony) {
// 	let roads: StructureRoad[] = [];
// 	let rootNode = colony.pos.findClosestByMultiRoomRange(room.roads);
//
// }
let RoadLogistics = RoadLogistics_1 = class RoadLogistics {
    constructor(colony) {
        this.colony = colony;
        this.ref = this.colony.name + ':roadLogistics';
        this.rooms = colony.rooms;
        this._assignedWorkers = {};
    }
    refresh() {
        this._assignedWorkers = {};
    }
    /* Whether a road in the network needs repair */
    workerShouldRepaveRoom(worker, room) {
        // Room should be repaved if there is a road with critical HP or if energy to repave >= worker carry capacity
        let otherAssignedWorkers = _.filter(this.assignedWorkers(room), name => name != worker.name);
        if (otherAssignedWorkers.length < RoadLogistics_1.settings.allowedPaversPerRoom) {
            if (this.assignedWorkers(room).includes(worker.name)) {
                // If worker is already working in the room, have it repair until all roads are at acceptable level
                return this.repairableRoads(room).length > 0;
            }
            else {
                // If worker is not already assigned, repair if critical roads or repaving energy >= carry capacity
                return this.criticalRoads(room).length > 0 || this.energyToRepave(room) >= worker.carryCapacity;
            }
        }
        else {
            return false;
        }
    }
    /* Get the room the worker should repave, if any */
    workerShouldRepave(worker) {
        // If the worker is already working in a room and should keep doing so, return that first
        if (worker.task && worker.task.name == repairTaskName) {
            let room = Game.rooms[worker.task.targetPos.roomName];
            if (room && this.assignedWorkers(room).includes(worker.name)
                && this.workerShouldRepaveRoom(worker, room)) {
                return room;
            }
        }
        // Otherwise scan through rooms and see if needs repaving
        for (let room of this.rooms) {
            if (this.workerShouldRepaveRoom(worker, room)) {
                return room;
            }
        }
    }
    // /* Compute roads ordered by a depth-first search from a root node */
    // roads(room: Room): StructureRoad[] {
    //
    // }
    criticalRoads(room) {
        return $.structures(this, 'criticalRoads:' + room.name, () => _.sortBy(_.filter(room.roads, road => road.hits < road.hitsMax * RoadLogistics_1.settings.criticalThreshold &&
            this.colony.roomPlanner.roadShouldBeHere(road.pos)), road => road.pos.getMultiRoomRangeTo(this.colony.pos)), ROAD_CACHE_TIMEOUT);
    }
    repairableRoads(room) {
        return $.structures(this, 'repairableRoads:' + room.name, () => _.sortBy(_.filter(room.roads, road => road.hits < road.hitsMax * RoadLogistics_1.settings.repairThreshold &&
            this.colony.roomPlanner.roadShouldBeHere(road.pos)), road => road.pos.getMultiRoomRangeTo(this.colony.pos)), ROAD_CACHE_TIMEOUT);
    }
    /* Total amount of energy needed to repair all roads in the room */
    energyToRepave(room) {
        return $.number(this, 'energyToRepave:' + room.name, () => _.sum(this.repairableRoads(room), road => (road.hitsMax - road.hits) / REPAIR_POWER));
    }
    /* Check that the worker is in the assignedWorker cache; avoids bugs where duplicate workers get assigned
     * on the same tick*/
    registerWorkerAssignment(worker, room) {
        if (this._assignedWorkers[room.name]) {
            if (!this._assignedWorkers[room.name].includes(worker.name)) {
                this._assignedWorkers[room.name].push(worker.name);
            }
        }
        else {
            this._assignedWorkers[room.name] = [worker.name];
        }
    }
    assignedWorkers(room) {
        return this._assignedWorkers[room.name] || [];
    }
    init() {
        let workers = this.colony.overlords.work.workers;
        for (let worker of workers) {
            if (worker.task && worker.task.name == repairTaskName) {
                let roomName = worker.task.targetPos.roomName;
                if (!this._assignedWorkers[roomName]) {
                    this._assignedWorkers[roomName] = [];
                }
                this._assignedWorkers[roomName].push(worker.name);
            }
        }
    }
    run() {
    }
};
RoadLogistics.settings = {
    allowedPaversPerRoom: 1,
    criticalThreshold: 0.25,
    repairThreshold: 0.9
};
RoadLogistics = RoadLogistics_1 = __decorate([
    profile
], RoadLogistics);

let Matcher = class Matcher {
    constructor(menPrefs, womenPrefs) {
        this.menPrefs = menPrefs;
        this.womenPrefs = womenPrefs;
        this.men = _.keys(menPrefs);
        this.women = _.keys(womenPrefs);
        this.menFree = _.zipObject(this.men, _.map(this.men, man => true));
        this.womenFree = _.zipObject(this.women, _.map(this.women, woman => true));
        this.couples = {};
    }
    /* Return whether the woman prefer man1 over man2 */
    prefers(woman, man1, man2) {
        return _.indexOf(this.womenPrefs[woman], man1) < _.indexOf(this.womenPrefs[woman], man2);
    }
    /* Engage a couple <3 */
    engage(man, woman) {
        this.menFree[man] = false;
        this.womenFree[woman] = false;
        _.remove(this.menPrefs[man], w => w == woman); // Remove the woman that the man proposed to
        // Don't remove from women prefs since we're matching from men side
        this.couples[man] = woman;
    }
    /* Break up a couple... </3 :'( */
    breakup(man, woman) {
        this.menFree[man] = true;
        this.womenFree[woman] = true;
        // Don't do anything to the preferences of men or women since they've already proposed
        delete this.couples[man];
    }
    /* Return the first free man who still has someone left to propose to */
    nextMan() {
        return _.find(this.men, man => this.menFree[man] && this.menPrefs[man].length > 0);
    }
    match() {
        let MAX_ITERATIONS = 1000;
        let count = 0;
        let man = this.nextMan();
        while (man) { // While there exists a free man who still has someone to propose to
            if (count > MAX_ITERATIONS) {
                console.log('Stable matching timed out!');
                return this.couples;
            }
            let woman = _.first(this.menPrefs[man]); // Get first woman on man's list
            if (this.womenFree[woman]) { // If woman is free, get engaged
                this.engage(man, woman);
            }
            else { // Else if woman prefers this man to her current, swap men
                let currentMan = _.findKey(this.couples, w => w == woman);
                if (this.prefers(woman, man, currentMan)) {
                    this.breakup(currentMan, woman);
                    this.engage(man, woman);
                }
                else {
                    _.remove(this.menPrefs[man], w => w == woman); // Record an unsuccessful proposal
                }
            }
            man = this.nextMan();
            count++;
        }
        return this.couples;
    }
};
Matcher = __decorate([
    profile
], Matcher);

'use strict';
var ansiRegex = function () {
	return /[\u001b\u009b][[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-PRZcf-nqry=><]/g;
};

var ansiRegex$1 = /*#__PURE__*/Object.freeze({
	default: ansiRegex,
	__moduleExports: ansiRegex
});

var require$$0 = ( ansiRegex$1 && ansiRegex ) || ansiRegex$1;

'use strict';
var ansiRegex$2 = require$$0();

var stripAnsi = function (str) {
	return typeof str === 'string' ? str.replace(ansiRegex$2, '') : str;
};

var stripAnsi$1 = /*#__PURE__*/Object.freeze({
	default: stripAnsi,
	__moduleExports: stripAnsi
});

var clone_1 = createCommonjsModule(function (module) {
var clone = (function() {
'use strict';

/**
 * Clones (copies) an Object using deep copying.
 *
 * This function supports circular references by default, but if you are certain
 * there are no circular references in your object, you can save some CPU time
 * by calling clone(obj, false).
 *
 * Caution: if `circular` is false and `parent` contains circular references,
 * your program may enter an infinite loop and crash.
 *
 * @param `parent` - the object to be cloned
 * @param `circular` - set to true if the object to be cloned may contain
 *    circular references. (optional - true by default)
 * @param `depth` - set to a number if the object is only to be cloned to
 *    a particular depth. (optional - defaults to Infinity)
 * @param `prototype` - sets the prototype to be used when cloning an object.
 *    (optional - defaults to parent prototype).
*/
function clone(parent, circular, depth, prototype) {
  var filter;
  if (typeof circular === 'object') {
    depth = circular.depth;
    prototype = circular.prototype;
    filter = circular.filter;
    circular = circular.circular;
  }
  // maintain two arrays for circular references, where corresponding parents
  // and children have the same index
  var allParents = [];
  var allChildren = [];

  var useBuffer = typeof Buffer != 'undefined';

  if (typeof circular == 'undefined')
    circular = true;

  if (typeof depth == 'undefined')
    depth = Infinity;

  // recurse this function so we don't reset allParents and allChildren
  function _clone(parent, depth) {
    // cloning null always returns null
    if (parent === null)
      return null;

    if (depth == 0)
      return parent;

    var child;
    var proto;
    if (typeof parent != 'object') {
      return parent;
    }

    if (clone.__isArray(parent)) {
      child = [];
    } else if (clone.__isRegExp(parent)) {
      child = new RegExp(parent.source, __getRegExpFlags(parent));
      if (parent.lastIndex) child.lastIndex = parent.lastIndex;
    } else if (clone.__isDate(parent)) {
      child = new Date(parent.getTime());
    } else if (useBuffer && Buffer.isBuffer(parent)) {
      if (Buffer.allocUnsafe) {
        // Node.js >= 4.5.0
        child = Buffer.allocUnsafe(parent.length);
      } else {
        // Older Node.js versions
        child = new Buffer(parent.length);
      }
      parent.copy(child);
      return child;
    } else {
      if (typeof prototype == 'undefined') {
        proto = Object.getPrototypeOf(parent);
        child = Object.create(proto);
      }
      else {
        child = Object.create(prototype);
        proto = prototype;
      }
    }

    if (circular) {
      var index = allParents.indexOf(parent);

      if (index != -1) {
        return allChildren[index];
      }
      allParents.push(parent);
      allChildren.push(child);
    }

    for (var i in parent) {
      var attrs;
      if (proto) {
        attrs = Object.getOwnPropertyDescriptor(proto, i);
      }

      if (attrs && attrs.set == null) {
        continue;
      }
      child[i] = _clone(parent[i], depth - 1);
    }

    return child;
  }

  return _clone(parent, depth);
}

/**
 * Simple flat clone using prototype, accepts only objects, usefull for property
 * override on FLAT configuration object (no nested props).
 *
 * USE WITH CAUTION! This may not behave as you wish if you do not know how this
 * works.
 */
clone.clonePrototype = function clonePrototype(parent) {
  if (parent === null)
    return null;

  var c = function () {};
  c.prototype = parent;
  return new c();
};

// private utility functions

function __objToStr(o) {
  return Object.prototype.toString.call(o);
}
clone.__objToStr = __objToStr;

function __isDate(o) {
  return typeof o === 'object' && __objToStr(o) === '[object Date]';
}
clone.__isDate = __isDate;

function __isArray(o) {
  return typeof o === 'object' && __objToStr(o) === '[object Array]';
}
clone.__isArray = __isArray;

function __isRegExp(o) {
  return typeof o === 'object' && __objToStr(o) === '[object RegExp]';
}
clone.__isRegExp = __isRegExp;

function __getRegExpFlags(re) {
  var flags = '';
  if (re.global) flags += 'g';
  if (re.ignoreCase) flags += 'i';
  if (re.multiline) flags += 'm';
  return flags;
}
clone.__getRegExpFlags = __getRegExpFlags;

return clone;
})();

if ('object' === 'object' && module.exports) {
  module.exports = clone;
}
});

var clone = /*#__PURE__*/Object.freeze({
	default: clone_1,
	__moduleExports: clone_1
});

var clone$1 = ( clone && clone_1 ) || clone;

var defaults = function(options, defaults) {
  options = options || {};

  Object.keys(defaults).forEach(function(key) {
    if (typeof options[key] === 'undefined') {
      options[key] = clone$1(defaults[key]);
    }
  });

  return options;
};

var defaults$1 = /*#__PURE__*/Object.freeze({
	default: defaults,
	__moduleExports: defaults
});

var combining = [
    [ 0x0300, 0x036F ], [ 0x0483, 0x0486 ], [ 0x0488, 0x0489 ],
    [ 0x0591, 0x05BD ], [ 0x05BF, 0x05BF ], [ 0x05C1, 0x05C2 ],
    [ 0x05C4, 0x05C5 ], [ 0x05C7, 0x05C7 ], [ 0x0600, 0x0603 ],
    [ 0x0610, 0x0615 ], [ 0x064B, 0x065E ], [ 0x0670, 0x0670 ],
    [ 0x06D6, 0x06E4 ], [ 0x06E7, 0x06E8 ], [ 0x06EA, 0x06ED ],
    [ 0x070F, 0x070F ], [ 0x0711, 0x0711 ], [ 0x0730, 0x074A ],
    [ 0x07A6, 0x07B0 ], [ 0x07EB, 0x07F3 ], [ 0x0901, 0x0902 ],
    [ 0x093C, 0x093C ], [ 0x0941, 0x0948 ], [ 0x094D, 0x094D ],
    [ 0x0951, 0x0954 ], [ 0x0962, 0x0963 ], [ 0x0981, 0x0981 ],
    [ 0x09BC, 0x09BC ], [ 0x09C1, 0x09C4 ], [ 0x09CD, 0x09CD ],
    [ 0x09E2, 0x09E3 ], [ 0x0A01, 0x0A02 ], [ 0x0A3C, 0x0A3C ],
    [ 0x0A41, 0x0A42 ], [ 0x0A47, 0x0A48 ], [ 0x0A4B, 0x0A4D ],
    [ 0x0A70, 0x0A71 ], [ 0x0A81, 0x0A82 ], [ 0x0ABC, 0x0ABC ],
    [ 0x0AC1, 0x0AC5 ], [ 0x0AC7, 0x0AC8 ], [ 0x0ACD, 0x0ACD ],
    [ 0x0AE2, 0x0AE3 ], [ 0x0B01, 0x0B01 ], [ 0x0B3C, 0x0B3C ],
    [ 0x0B3F, 0x0B3F ], [ 0x0B41, 0x0B43 ], [ 0x0B4D, 0x0B4D ],
    [ 0x0B56, 0x0B56 ], [ 0x0B82, 0x0B82 ], [ 0x0BC0, 0x0BC0 ],
    [ 0x0BCD, 0x0BCD ], [ 0x0C3E, 0x0C40 ], [ 0x0C46, 0x0C48 ],
    [ 0x0C4A, 0x0C4D ], [ 0x0C55, 0x0C56 ], [ 0x0CBC, 0x0CBC ],
    [ 0x0CBF, 0x0CBF ], [ 0x0CC6, 0x0CC6 ], [ 0x0CCC, 0x0CCD ],
    [ 0x0CE2, 0x0CE3 ], [ 0x0D41, 0x0D43 ], [ 0x0D4D, 0x0D4D ],
    [ 0x0DCA, 0x0DCA ], [ 0x0DD2, 0x0DD4 ], [ 0x0DD6, 0x0DD6 ],
    [ 0x0E31, 0x0E31 ], [ 0x0E34, 0x0E3A ], [ 0x0E47, 0x0E4E ],
    [ 0x0EB1, 0x0EB1 ], [ 0x0EB4, 0x0EB9 ], [ 0x0EBB, 0x0EBC ],
    [ 0x0EC8, 0x0ECD ], [ 0x0F18, 0x0F19 ], [ 0x0F35, 0x0F35 ],
    [ 0x0F37, 0x0F37 ], [ 0x0F39, 0x0F39 ], [ 0x0F71, 0x0F7E ],
    [ 0x0F80, 0x0F84 ], [ 0x0F86, 0x0F87 ], [ 0x0F90, 0x0F97 ],
    [ 0x0F99, 0x0FBC ], [ 0x0FC6, 0x0FC6 ], [ 0x102D, 0x1030 ],
    [ 0x1032, 0x1032 ], [ 0x1036, 0x1037 ], [ 0x1039, 0x1039 ],
    [ 0x1058, 0x1059 ], [ 0x1160, 0x11FF ], [ 0x135F, 0x135F ],
    [ 0x1712, 0x1714 ], [ 0x1732, 0x1734 ], [ 0x1752, 0x1753 ],
    [ 0x1772, 0x1773 ], [ 0x17B4, 0x17B5 ], [ 0x17B7, 0x17BD ],
    [ 0x17C6, 0x17C6 ], [ 0x17C9, 0x17D3 ], [ 0x17DD, 0x17DD ],
    [ 0x180B, 0x180D ], [ 0x18A9, 0x18A9 ], [ 0x1920, 0x1922 ],
    [ 0x1927, 0x1928 ], [ 0x1932, 0x1932 ], [ 0x1939, 0x193B ],
    [ 0x1A17, 0x1A18 ], [ 0x1B00, 0x1B03 ], [ 0x1B34, 0x1B34 ],
    [ 0x1B36, 0x1B3A ], [ 0x1B3C, 0x1B3C ], [ 0x1B42, 0x1B42 ],
    [ 0x1B6B, 0x1B73 ], [ 0x1DC0, 0x1DCA ], [ 0x1DFE, 0x1DFF ],
    [ 0x200B, 0x200F ], [ 0x202A, 0x202E ], [ 0x2060, 0x2063 ],
    [ 0x206A, 0x206F ], [ 0x20D0, 0x20EF ], [ 0x302A, 0x302F ],
    [ 0x3099, 0x309A ], [ 0xA806, 0xA806 ], [ 0xA80B, 0xA80B ],
    [ 0xA825, 0xA826 ], [ 0xFB1E, 0xFB1E ], [ 0xFE00, 0xFE0F ],
    [ 0xFE20, 0xFE23 ], [ 0xFEFF, 0xFEFF ], [ 0xFFF9, 0xFFFB ],
    [ 0x10A01, 0x10A03 ], [ 0x10A05, 0x10A06 ], [ 0x10A0C, 0x10A0F ],
    [ 0x10A38, 0x10A3A ], [ 0x10A3F, 0x10A3F ], [ 0x1D167, 0x1D169 ],
    [ 0x1D173, 0x1D182 ], [ 0x1D185, 0x1D18B ], [ 0x1D1AA, 0x1D1AD ],
    [ 0x1D242, 0x1D244 ], [ 0xE0001, 0xE0001 ], [ 0xE0020, 0xE007F ],
    [ 0xE0100, 0xE01EF ]
];

var combining$1 = /*#__PURE__*/Object.freeze({
	default: combining,
	__moduleExports: combining
});

var defaults$2 = ( defaults$1 && defaults ) || defaults$1;

var combining$2 = ( combining$1 && combining ) || combining$1;

"use strict";




var DEFAULTS = {
  nul: 0,
  control: 0
};

var wcwidth_1 = function wcwidth(str) {
  return wcswidth(str, DEFAULTS)
};

var config = function(opts) {
  opts = defaults$2(opts || {}, DEFAULTS);
  return function wcwidth(str) {
    return wcswidth(str, opts)
  }
};

/*
 *  The following functions define the column width of an ISO 10646
 *  character as follows:
 *  - The null character (U+0000) has a column width of 0.
 *  - Other C0/C1 control characters and DEL will lead to a return value
 *    of -1.
 *  - Non-spacing and enclosing combining characters (general category
 *    code Mn or Me in the
 *    Unicode database) have a column width of 0.
 *  - SOFT HYPHEN (U+00AD) has a column width of 1.
 *  - Other format characters (general category code Cf in the Unicode
 *    database) and ZERO WIDTH
 *    SPACE (U+200B) have a column width of 0.
 *  - Hangul Jamo medial vowels and final consonants (U+1160-U+11FF)
 *    have a column width of 0.
 *  - Spacing characters in the East Asian Wide (W) or East Asian
 *    Full-width (F) category as
 *    defined in Unicode Technical Report #11 have a column width of 2.
 *  - All remaining characters (including all printable ISO 8859-1 and
 *    WGL4 characters, Unicode control characters, etc.) have a column
 *    width of 1.
 *  This implementation assumes that characters are encoded in ISO 10646.
*/

function wcswidth(str, opts) {
  if (typeof str !== 'string') return wcwidth(str, opts)

  var s = 0;
  for (var i = 0; i < str.length; i++) {
    var n = wcwidth(str.charCodeAt(i), opts);
    if (n < 0) return -1
    s += n;
  }

  return s
}

function wcwidth(ucs, opts) {
  // test for 8-bit control characters
  if (ucs === 0) return opts.nul
  if (ucs < 32 || (ucs >= 0x7f && ucs < 0xa0)) return opts.control

  // binary search in table of non-spacing characters
  if (bisearch(ucs)) return 0

  // if we arrive here, ucs is not a combining or C0/C1 control character
  return 1 +
      (ucs >= 0x1100 &&
       (ucs <= 0x115f ||                       // Hangul Jamo init. consonants
        ucs == 0x2329 || ucs == 0x232a ||
        (ucs >= 0x2e80 && ucs <= 0xa4cf &&
         ucs != 0x303f) ||                     // CJK ... Yi
        (ucs >= 0xac00 && ucs <= 0xd7a3) ||    // Hangul Syllables
        (ucs >= 0xf900 && ucs <= 0xfaff) ||    // CJK Compatibility Ideographs
        (ucs >= 0xfe10 && ucs <= 0xfe19) ||    // Vertical forms
        (ucs >= 0xfe30 && ucs <= 0xfe6f) ||    // CJK Compatibility Forms
        (ucs >= 0xff00 && ucs <= 0xff60) ||    // Fullwidth Forms
        (ucs >= 0xffe0 && ucs <= 0xffe6) ||
        (ucs >= 0x20000 && ucs <= 0x2fffd) ||
        (ucs >= 0x30000 && ucs <= 0x3fffd)));
}

function bisearch(ucs) {
  var min = 0;
  var max = combining$2.length - 1;
  var mid;

  if (ucs < combining$2[0][0] || ucs > combining$2[max][1]) return false

  while (max >= min) {
    mid = Math.floor((min + max) / 2);
    if (ucs > combining$2[mid][1]) min = mid + 1;
    else if (ucs < combining$2[mid][0]) max = mid - 1;
    else return true
  }

  return false
}
wcwidth_1.config = config;

var wcwidth$1 = /*#__PURE__*/Object.freeze({
	default: wcwidth_1,
	__moduleExports: wcwidth_1,
	config: config
});

var stripAnsi$2 = ( stripAnsi$1 && stripAnsi ) || stripAnsi$1;

var wcwidth$2 = ( wcwidth$1 && wcwidth_1 ) || wcwidth$1;

var width = function(str) {
  return wcwidth$2(stripAnsi$2(str))
};

var width$1 = /*#__PURE__*/Object.freeze({
	default: width,
	__moduleExports: width
});

var wcwidth$3 = ( width$1 && width ) || width$1;

"use strict";



/**
 * repeat string `str` up to total length of `len`
 *
 * @param String str string to repeat
 * @param Number len total length of output string
 */

function repeatString(str, len) {
  return Array.apply(null, {length: len + 1}).join(str).slice(0, len)
}

/**
 * Pad `str` up to total length `max` with `chr`.
 * If `str` is longer than `max`, padRight will return `str` unaltered.
 *
 * @param String str string to pad
 * @param Number max total length of output string
 * @param String chr optional. Character to pad with. default: ' '
 * @return String padded str
 */

function padRight(str, max, chr) {
  str = str != null ? str : '';
  str = String(str);
  var length = max - wcwidth$3(str);
  if (length <= 0) return str
  return str + repeatString(chr || ' ', length)
}

/**
 * Pad `str` up to total length `max` with `chr`.
 * If `str` is longer than `max`, padCenter will return `str` unaltered.
 *
 * @param String str string to pad
 * @param Number max total length of output string
 * @param String chr optional. Character to pad with. default: ' '
 * @return String padded str
 */

function padCenter(str, max, chr) {
  str = str != null ? str : '';
  str = String(str);
  var length = max - wcwidth$3(str);
  if (length <= 0) return str
  var lengthLeft = Math.floor(length/2);
  var lengthRight = length - lengthLeft;
  return repeatString(chr || ' ', lengthLeft) + str + repeatString(chr || ' ', lengthRight)
}

/**
 * Pad `str` up to total length `max` with `chr`, on the left.
 * If `str` is longer than `max`, padRight will return `str` unaltered.
 *
 * @param String str string to pad
 * @param Number max total length of output string
 * @param String chr optional. Character to pad with. default: ' '
 * @return String padded str
 */

function padLeft(str, max, chr) {
  str = str != null ? str : '';
  str = String(str);
  var length = max - wcwidth$3(str);
  if (length <= 0) return str
  return repeatString(chr || ' ', length) + str
}

/**
 * Split a String `str` into lines of maxiumum length `max`.
 * Splits on word boundaries. Preserves existing new lines.
 *
 * @param String str string to split
 * @param Number max length of each line
 * @return Array Array containing lines.
 */

function splitIntoLines(str, max) {
  function _splitIntoLines(str, max) {
    return str.trim().split(' ').reduce(function(lines, word) {
      var line = lines[lines.length - 1];
      if (line && wcwidth$3(line.join(' ')) + wcwidth$3(word) < max) {
        lines[lines.length - 1].push(word); // add to line
      }
      else lines.push([word]); // new line
      return lines
    }, []).map(function(l) {
      return l.join(' ')
    })
  }
  return str.split('\n').map(function(str) {
    return _splitIntoLines(str, max)
  }).reduce(function(lines, line) {
    return lines.concat(line)
  }, [])
}

/**
 * Add spaces and `truncationChar` between words of
 * `str` which are longer than `max`.
 *
 * @param String str string to split
 * @param Number max length of each line
 * @param Number truncationChar character to append to split words
 * @return String
 */

function splitLongWords(str, max, truncationChar) {
  str = str.trim();
  var result = [];
  var words = str.split(' ');
  var remainder = '';

  var truncationWidth = wcwidth$3(truncationChar);

  while (remainder || words.length) {
    if (remainder) {
      var word = remainder;
      remainder = '';
    } else {
      var word = words.shift();
    }

    if (wcwidth$3(word) > max) {
      // slice is based on length no wcwidth
      var i = 0;
      var wwidth = 0;
      var limit = max - truncationWidth;
      while (i < word.length) {
        var w = wcwidth$3(word.charAt(i));
        if (w + wwidth > limit) {
          break
        }
        wwidth += w;
        ++i;
      }

      remainder = word.slice(i); // get remainder
      // save remainder for next loop

      word = word.slice(0, i); // grab truncated word
      word += truncationChar; // add trailing … or whatever
    }
    result.push(word);
  }

  return result.join(' ')
}


/**
 * Truncate `str` into total width `max`
 * If `str` is shorter than `max`,  will return `str` unaltered.
 *
 * @param String str string to truncated
 * @param Number max total wcwidth of output string
 * @return String truncated str
 */

function truncateString(str, max) {

  str = str != null ? str : '';
  str = String(str);

  if(max == Infinity) return str

  var i = 0;
  var wwidth = 0;
  while (i < str.length) {
    var w = wcwidth$3(str.charAt(i));
    if(w + wwidth > max)
      break
    wwidth += w;
    ++i;
  }
  return str.slice(0, i)
}



/**
 * Exports
 */

var padRight_1 = padRight;
var padCenter_1 = padCenter;
var padLeft_1 = padLeft;
var splitIntoLines_1 = splitIntoLines;
var splitLongWords_1 = splitLongWords;
var truncateString_1 = truncateString;

var utils = {
	padRight: padRight_1,
	padCenter: padCenter_1,
	padLeft: padLeft_1,
	splitIntoLines: splitIntoLines_1,
	splitLongWords: splitLongWords_1,
	truncateString: truncateString_1
};

var utils$1 = /*#__PURE__*/Object.freeze({
	default: utils,
	__moduleExports: utils,
	padRight: padRight_1,
	padCenter: padCenter_1,
	padLeft: padLeft_1,
	splitIntoLines: splitIntoLines_1,
	splitLongWords: splitLongWords_1,
	truncateString: truncateString_1
});

var _require = ( utils$1 && utils ) || utils$1;

"use strict";





var padRight$1 = _require.padRight;
var padCenter$1 = _require.padCenter;
var padLeft$1 = _require.padLeft;
var splitIntoLines$1 = _require.splitIntoLines;
var splitLongWords$1 = _require.splitLongWords;
var truncateString$1 = _require.truncateString;

var DEFAULT_HEADING_TRANSFORM = function DEFAULT_HEADING_TRANSFORM(key) {
  return key.toUpperCase();
};

var DEFAULT_DATA_TRANSFORM = function DEFAULT_DATA_TRANSFORM(cell, column, index) {
  return cell;
};

var DEFAULTS$1 = Object.freeze({
  maxWidth: Infinity,
  minWidth: 0,
  columnSplitter: ' ',
  truncate: false,
  truncateMarker: '…',
  preserveNewLines: false,
  paddingChr: ' ',
  showHeaders: true,
  headingTransform: DEFAULT_HEADING_TRANSFORM,
  dataTransform: DEFAULT_DATA_TRANSFORM
});

var columnify = function (items) {
  var options = arguments.length <= 1 || arguments[1] === undefined ? {} : arguments[1];

  var columnConfigs = options.config || {};
  delete options.config; // remove config so doesn't appear on every column.

  var maxLineWidth = options.maxLineWidth || Infinity;
  if (maxLineWidth === 'auto') maxLineWidth = process.stdout.columns || Infinity;
  delete options.maxLineWidth; // this is a line control option, don't pass it to column

  // Option defaults inheritance:
  // options.config[columnName] => options => DEFAULTS
  options = mixin({}, DEFAULTS$1, options);

  options.config = options.config || Object.create(null);

  options.spacing = options.spacing || '\n'; // probably useless
  options.preserveNewLines = !!options.preserveNewLines;
  options.showHeaders = !!options.showHeaders;
  options.columns = options.columns || options.include; // alias include/columns, prefer columns if supplied
  var columnNames = options.columns || []; // optional user-supplied columns to include

  items = toArray(items, columnNames);

  // if not suppled column names, automatically determine columns from data keys
  if (!columnNames.length) {
    items.forEach(function (item) {
      for (var columnName in item) {
        if (columnNames.indexOf(columnName) === -1) columnNames.push(columnName);
      }
    });
  }

  // initialize column defaults (each column inherits from options.config)
  var columns = columnNames.reduce(function (columns, columnName) {
    var column = Object.create(options);
    columns[columnName] = mixin(column, columnConfigs[columnName]);
    return columns;
  }, Object.create(null));

  // sanitize column settings
  columnNames.forEach(function (columnName) {
    var column = columns[columnName];
    column.name = columnName;
    column.maxWidth = Math.ceil(column.maxWidth);
    column.minWidth = Math.ceil(column.minWidth);
    column.truncate = !!column.truncate;
    column.align = column.align || 'left';
  });

  // sanitize data
  items = items.map(function (item) {
    var result = Object.create(null);
    columnNames.forEach(function (columnName) {
      // null/undefined -> ''
      result[columnName] = item[columnName] != null ? item[columnName] : '';
      // toString everything
      result[columnName] = '' + result[columnName];
      if (columns[columnName].preserveNewLines) {
        // merge non-newline whitespace chars
        result[columnName] = result[columnName].replace(/[^\S\n]/gmi, ' ');
      } else {
        // merge all whitespace chars
        result[columnName] = result[columnName].replace(/\s/gmi, ' ');
      }
    });
    return result;
  });

  // transform data cells
  columnNames.forEach(function (columnName) {
    var column = columns[columnName];
    items = items.map(function (item, index) {
      var col = Object.create(column);
      item[columnName] = column.dataTransform(item[columnName], col, index);

      var changedKeys = Object.keys(col);
      // disable default heading transform if we wrote to column.name
      if (changedKeys.indexOf('name') !== -1) {
        if (column.headingTransform !== DEFAULT_HEADING_TRANSFORM) return;
        column.headingTransform = function (heading) {
          return heading;
        };
      }
      changedKeys.forEach(function (key) {
        return column[key] = col[key];
      });
      return item;
    });
  });

  // add headers
  var headers = {};
  if (options.showHeaders) {
    columnNames.forEach(function (columnName) {
      var column = columns[columnName];

      if (!column.showHeaders) {
        headers[columnName] = '';
        return;
      }

      headers[columnName] = column.headingTransform(column.name);
    });
    items.unshift(headers);
  }
  // get actual max-width between min & max
  // based on length of data in columns
  columnNames.forEach(function (columnName) {
    var column = columns[columnName];
    column.width = items.map(function (item) {
      return item[columnName];
    }).reduce(function (min, cur) {
      // if already at maxWidth don't bother testing
      if (min >= column.maxWidth) return min;
      return Math.max(min, Math.min(column.maxWidth, Math.max(column.minWidth, wcwidth$3(cur))));
    }, 0);
  });

  // split long words so they can break onto multiple lines
  columnNames.forEach(function (columnName) {
    var column = columns[columnName];
    items = items.map(function (item) {
      item[columnName] = splitLongWords$1(item[columnName], column.width, column.truncateMarker);
      return item;
    });
  });

  // wrap long lines. each item is now an array of lines.
  columnNames.forEach(function (columnName) {
    var column = columns[columnName];
    items = items.map(function (item, index) {
      var cell = item[columnName];
      item[columnName] = splitIntoLines$1(cell, column.width);

      // if truncating required, only include first line + add truncation char
      if (column.truncate && item[columnName].length > 1) {
        item[columnName] = splitIntoLines$1(cell, column.width - wcwidth$3(column.truncateMarker));
        var firstLine = item[columnName][0];
        if (!endsWith(firstLine, column.truncateMarker)) item[columnName][0] += column.truncateMarker;
        item[columnName] = item[columnName].slice(0, 1);
      }
      return item;
    });
  });

  // recalculate column widths from truncated output/lines
  columnNames.forEach(function (columnName) {
    var column = columns[columnName];
    column.width = items.map(function (item) {
      return item[columnName].reduce(function (min, cur) {
        if (min >= column.maxWidth) return min;
        return Math.max(min, Math.min(column.maxWidth, Math.max(column.minWidth, wcwidth$3(cur))));
      }, 0);
    }).reduce(function (min, cur) {
      if (min >= column.maxWidth) return min;
      return Math.max(min, Math.min(column.maxWidth, Math.max(column.minWidth, cur)));
    }, 0);
  });

  var rows = createRows(items, columns, columnNames, options.paddingChr); // merge lines into rows
  // conceive output
  return rows.reduce(function (output, row) {
    return output.concat(row.reduce(function (rowOut, line) {
      return rowOut.concat(line.join(options.columnSplitter));
    }, []));
  }, []).map(function (line) {
    return truncateString$1(line, maxLineWidth);
  }).join(options.spacing);
};

/**
 * Convert wrapped lines into rows with padded values.
 *
 * @param Array items data to process
 * @param Array columns column width settings for wrapping
 * @param Array columnNames column ordering
 * @return Array items wrapped in arrays, corresponding to lines
 */

function createRows(items, columns, columnNames, paddingChr) {
  return items.map(function (item) {
    var row = [];
    var numLines = 0;
    columnNames.forEach(function (columnName) {
      numLines = Math.max(numLines, item[columnName].length);
    });
    // combine matching lines of each rows

    var _loop = function _loop(i) {
      row[i] = row[i] || [];
      columnNames.forEach(function (columnName) {
        var column = columns[columnName];
        var val = item[columnName][i] || ''; // || '' ensures empty columns get padded
        if (column.align === 'right') row[i].push(padLeft$1(val, column.width, paddingChr));else if (column.align === 'center' || column.align === 'centre') row[i].push(padCenter$1(val, column.width, paddingChr));else row[i].push(padRight$1(val, column.width, paddingChr));
      });
    };

    for (var i = 0; i < numLines; i++) {
      _loop(i);
    }
    return row;
  });
}

/**
 * Object.assign
 *
 * @return Object Object with properties mixed in.
 */

function mixin() {
  var _Object;

  if (Object.assign) return (_Object = Object).assign.apply(_Object, arguments);
  return ObjectAssign.apply(undefined, arguments);
}

function ObjectAssign(target, firstSource) {
  "use strict";

  if (target === undefined || target === null) throw new TypeError("Cannot convert first argument to object");

  var to = Object(target);

  var hasPendingException = false;
  var pendingException;

  for (var i = 1; i < arguments.length; i++) {
    var nextSource = arguments[i];
    if (nextSource === undefined || nextSource === null) continue;

    var keysArray = Object.keys(Object(nextSource));
    for (var nextIndex = 0, len = keysArray.length; nextIndex < len; nextIndex++) {
      var nextKey = keysArray[nextIndex];
      try {
        var desc = Object.getOwnPropertyDescriptor(nextSource, nextKey);
        if (desc !== undefined && desc.enumerable) to[nextKey] = nextSource[nextKey];
      } catch (e) {
        if (!hasPendingException) {
          hasPendingException = true;
          pendingException = e;
        }
      }
    }

    if (hasPendingException) throw pendingException;
  }
  return to;
}

/**
 * Adapted from String.prototype.endsWith polyfill.
 */

function endsWith(target, searchString, position) {
  position = position || target.length;
  position = position - searchString.length;
  var lastIndex = target.lastIndexOf(searchString);
  return lastIndex !== -1 && lastIndex === position;
}

function toArray(items, columnNames) {
  if (Array.isArray(items)) return items;
  var rows = [];
  for (var key in items) {
    var item = {};
    item[columnNames[0] || 'key'] = key;
    item[columnNames[1] || 'value'] = items[key];
    rows.push(item);
  }
  return rows;
}
var columnify_1 = columnify.columnify;

// Logistics Group: efficiently partners resource requests with transporters using a stable matching algorithm to
var LogisticsNetwork_1;
// | DirectivePickup// | Zerg;
const ALL_RESOURCE_TYPE_ERROR = `Improper logistics request: 'all' can only be used for store structure or tombstone!`;
const LogisticsNetworkMemoryDefaults = {
    transporterCache: {},
};
let LogisticsNetwork = LogisticsNetwork_1 = class LogisticsNetwork {
    constructor(colony) {
        this.memory = Mem.wrap(colony.memory, 'logisticsNetwork', LogisticsNetworkMemoryDefaults);
        this.requests = [];
        this.targetToRequest = {};
        this.colony = colony;
        // this.transporters = _.filter(colony.getCreepsByRole(TransporterSetup.role),
        // 							 creep => !creep.spawning &&
        // 									  creep.carryCapacity >= LogisticsNetwork.settings.carryThreshold);
        this.buffers = _.compact([colony.storage, colony.terminal]);
        this.cache = {
            nextAvailability: {},
            predictedTransporterCarry: {},
            resourceChangeRate: {}
        };
        // this.logisticPositions = {};
        // for (let room of this.colony.rooms) {
        // 	this.logisticPositions[room.name] = _.map([...room.storageUnits, ...room.links], s => s.pos);
        // }
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'logisticsNetwork', LogisticsNetworkMemoryDefaults);
        this.requests = [];
        this.targetToRequest = {};
        this._matching = undefined;
        this.cache = {
            nextAvailability: {},
            predictedTransporterCarry: {},
            resourceChangeRate: {}
        };
    }
    // Request and provide functions ===================================================================================
    /* Request for resources to be deposited into this target */
    requestInput(target, opts = {}) {
        _.defaults(opts, {
            resourceType: RESOURCE_ENERGY,
            multiplier: 1,
            dAmountdt: 0,
        });
        if (target.room != this.colony.room) {
            log.warning(`${target.ref} at ${target.pos.print} is outside colony room; shouldn't request!`);
            return;
        }
        if (opts.resourceType == 'all') {
            log.warning(`Logistics request error: 'all' can only be used for output requests`);
            return;
        }
        if (!opts.amount) {
            opts.amount = this.getInputAmount(target, opts.resourceType);
        }
        // Register the request
        let requestID = this.requests.length;
        let req = {
            id: requestID.toString(),
            target: target,
            amount: opts.amount,
            dAmountdt: opts.dAmountdt,
            resourceType: opts.resourceType,
            multiplier: opts.multiplier,
        };
        this.requests.push(req);
        this.targetToRequest[req.target.ref] = requestID;
    }
    /* Request for resources to be withdrawn from this target */
    requestOutput(target, opts = {}) {
        _.defaults(opts, {
            resourceType: RESOURCE_ENERGY,
            multiplier: 1,
            dAmountdt: 0,
        });
        if (opts.resourceType == 'all' && (isStoreStructure(target) || isTombstone(target))) {
            if (_.sum(target.store) == target.store.energy) {
                opts.resourceType = RESOURCE_ENERGY; // convert "all" requests to energy if that's all they have
            }
        }
        if (!opts.amount) {
            opts.amount = this.getOutputAmount(target, opts.resourceType);
        }
        opts.amount *= -1;
        (opts.dAmountdt) *= -1;
        // Register the request
        let requestID = this.requests.length;
        let req = {
            id: requestID.toString(),
            target: target,
            amount: opts.amount,
            dAmountdt: opts.dAmountdt,
            resourceType: opts.resourceType,
            multiplier: opts.multiplier,
        };
        this.requests.push(req);
        this.targetToRequest[req.target.ref] = requestID;
    }
    /* Requests output for every mineral in a requestor object */
    requestOutputMinerals(target, opts = {}) {
        for (let resourceType in target.store) {
            if (resourceType == RESOURCE_ENERGY)
                continue;
            let amount = target.store[resourceType] || 0;
            if (amount > 0) {
                opts.resourceType = resourceType;
                this.requestOutput(target, opts);
            }
        }
    }
    getInputAmount(target, resourceType) {
        // if (target instanceof DirectivePickup) {
        // 	return target.storeCapacity - _.sum(target.store);
        // } else
        if (isResource(target) || isTombstone(target)) {
            log.error(`Improper logistics request: should not request input for resource or tombstone!`);
            return 0;
        }
        else if (isStoreStructure(target)) {
            return target.storeCapacity - _.sum(target.store);
        }
        else if (isEnergyStructure(target) && resourceType == RESOURCE_ENERGY) {
            return target.energyCapacity - target.energy;
        }
        // else if (target instanceof Zerg) {
        // 	return target.carryCapacity - _.sum(target.carry);
        // }
        else {
            if (target instanceof StructureLab) {
                if (resourceType == target.mineralType) {
                    return target.mineralCapacity - target.mineralAmount;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energyCapacity - target.energy;
                }
            }
            else if (target instanceof StructureNuker) {
                if (resourceType == RESOURCE_GHODIUM) {
                    return target.ghodiumCapacity - target.ghodium;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energyCapacity - target.energy;
                }
            }
            else if (target instanceof StructurePowerSpawn) {
                if (resourceType == RESOURCE_POWER) {
                    return target.powerCapacity - target.power;
                }
                else if (resourceType == RESOURCE_ENERGY) {
                    return target.energyCapacity - target.energy;
                }
            }
        }
        log.warning('Could not determine input amount!');
        return 0;
    }
    getOutputAmount(target, resourceType) {
        if (resourceType == 'all') {
            if (isTombstone(target) || isStoreStructure(target)) {
                return _.sum(target.store);
            }
            else {
                log.error(ALL_RESOURCE_TYPE_ERROR);
                return 0;
            }
        }
        else {
            if (isResource(target)) {
                return target.amount;
            }
            else if (isTombstone(target)) {
                return target.store[resourceType] || 0;
            }
            else if (isStoreStructure(target)) {
                return target.store[resourceType] || 0;
            }
            else if (isEnergyStructure(target) && resourceType == RESOURCE_ENERGY) {
                return target.energy;
            }
            // else if (target instanceof Zerg) {
            // 	return target.carry[resourceType]!;
            // }
            else {
                if (target instanceof StructureLab) {
                    if (resourceType == target.mineralType) {
                        return target.mineralAmount;
                    }
                    else if (resourceType == RESOURCE_ENERGY) {
                        return target.energy;
                    }
                }
                else if (target instanceof StructureNuker) {
                    if (resourceType == RESOURCE_GHODIUM) {
                        return target.ghodium;
                    }
                    else if (resourceType == RESOURCE_ENERGY) {
                        return target.energy;
                    }
                }
                else if (target instanceof StructurePowerSpawn) {
                    if (resourceType == RESOURCE_POWER) {
                        return target.power;
                    }
                    else if (resourceType == RESOURCE_ENERGY) {
                        return target.energy;
                    }
                }
            }
        }
        log.warning('Could not determine output amount!');
        return 0;
    }
    // Transporter availability and predictive functions ===============================================================
    computeNextAvailability(transporter) {
        if (transporter.task) {
            let approximateDistance = transporter.task.eta;
            let pos = transporter.pos;
            let targetPositions = transporter.task.targetPosManifest;
            // If there is a well-defined task ETA, use that as the first leg, else set dist to zero and use range
            if (approximateDistance) {
                for (let targetPos of targetPositions.slice(1)) {
                    // The path lengths between any two logistics targets should be well-memorized
                    approximateDistance += Math.ceil(pos.getMultiRoomRangeTo(targetPos)
                        * LogisticsNetwork_1.settings.rangeToPathHeuristic);
                    // approximateDistance += Pathing.distance(pos, targetPos);
                    pos = targetPos;
                }
            }
            else {
                // This probably shouldn't happen...
                approximateDistance = 0;
                for (let targetPos of targetPositions) {
                    approximateDistance += Math.ceil(pos.getMultiRoomRangeTo(targetPos)
                        * LogisticsNetwork_1.settings.rangeToPathHeuristic);
                    // approximateDistance += Pathing.distance(pos, targetPos);
                    pos = targetPos;
                }
            }
            return [approximateDistance, pos];
        }
        else {
            // Report the transporter as being near a logistics target so that Pathing.distance() won't waste CPU
            // let nearbyLogisticPositions = transporter.pos.findInRange(this.logisticPositions[transporter.room.name], 2);
            return [0, transporter.pos];
        }
    }
    /* Number of ticks until the transporter is available and where it will be */
    nextAvailability(transporter) {
        if (!this.cache.nextAvailability[transporter.name]) {
            this.cache.nextAvailability[transporter.name] = this.computeNextAvailability(transporter);
        }
        return this.cache.nextAvailability[transporter.name];
    }
    static targetingTransporters(target, excludedTransporter) {
        const targetingZerg = _.map(target.targetedBy, name => Overmind.zerg[name]);
        const targetingTransporters = _.filter(targetingZerg, zerg => zerg.roleName == Roles.transport);
        if (excludedTransporter)
            _.remove(targetingTransporters, transporter => transporter.name == excludedTransporter.name);
        return targetingTransporters;
    }
    /* Returns the predicted state of the transporter's carry after completing its current task */
    computePredictedTransporterCarry(transporter, nextAvailability) {
        if (transporter.task && transporter.task.target) {
            let requestID = this.targetToRequest[transporter.task.target.ref];
            if (requestID) {
                let request = this.requests[requestID];
                if (request) {
                    let carry = transporter.carry;
                    let remainingCapacity = transporter.carryCapacity - _.sum(carry);
                    let resourceAmount = -1 * this.predictedRequestAmount(transporter, request, nextAvailability);
                    // ^ need to multiply amount by -1 since transporter is doing complement of what request needs
                    if (request.resourceType == 'all') {
                        if (!isStoreStructure(request.target) && !isTombstone(request.target)) {
                            log.error(ALL_RESOURCE_TYPE_ERROR);
                            return { energy: 0 };
                        }
                        for (let resourceType in request.target.store) {
                            let resourceFraction = (request.target.store[resourceType] || 0)
                                / _.sum(request.target.store);
                            if (carry[resourceType]) {
                                carry[resourceType] += resourceAmount * resourceFraction;
                                carry[resourceType] = minMax(carry[resourceType], 0, remainingCapacity);
                            }
                            else {
                                carry[resourceType] = minMax(resourceAmount, 0, remainingCapacity);
                            }
                        }
                    }
                    else {
                        if (carry[request.resourceType]) {
                            carry[request.resourceType] += resourceAmount;
                            carry[request.resourceType] = minMax(carry[request.resourceType], 0, remainingCapacity);
                        }
                        else {
                            carry[request.resourceType] = minMax(resourceAmount, 0, remainingCapacity);
                        }
                    }
                    return carry;
                }
            }
        }
        return transporter.carry;
    }
    /* Returns the predicted state of the transporter's carry after completing its task */
    predictedTransporterCarry(transporter) {
        if (!this.cache.predictedTransporterCarry[transporter.name]) {
            this.cache.predictedTransporterCarry[transporter.name] = this.computePredictedTransporterCarry(transporter);
        }
        return this.cache.predictedTransporterCarry[transporter.name];
    }
    /* Returns the effective amount that a transporter will see upon arrival, accounting for other targeting creeps */
    predictedRequestAmount(transporter, request, nextAvailability) {
        // Figure out when/where the transporter will be free
        let busyUntil;
        let newPos;
        if (!nextAvailability) {
            [busyUntil, newPos] = this.nextAvailability(transporter);
        }
        else {
            [busyUntil, newPos] = nextAvailability;
        }
        // let eta = busyUntil + Pathing.distance(newPos, request.target.pos);
        let eta = busyUntil + LogisticsNetwork_1.settings.rangeToPathHeuristic *
            newPos.getMultiRoomRangeTo(request.target.pos);
        let predictedDifference = request.dAmountdt * eta; // dAmountdt has same sign as amount
        // Account for other transporters targeting the target
        let otherTargetingTransporters = LogisticsNetwork_1.targetingTransporters(request.target, transporter);
        // let closerTargetingTransporters = _.filter(otherTargetingTransporters,
        // 										   transporter => this.nextAvailability(transporter)[0] < eta);
        if (request.amount > 0) { // input state, resources into target
            let predictedAmount = request.amount + predictedDifference;
            if (isStoreStructure(request.target)) { // cap predicted amount at storeCapacity
                predictedAmount = Math.min(predictedAmount, request.target.storeCapacity);
            }
            else if (isEnergyStructure(request.target)) {
                predictedAmount = Math.min(predictedAmount, request.target.energyCapacity);
            }
            let resourceInflux = _.sum(_.map(otherTargetingTransporters, other => (other.carry[request.resourceType] || 0)));
            predictedAmount = Math.max(predictedAmount - resourceInflux, 0);
            return predictedAmount;
        }
        else { // output state, resources withdrawn from target
            let predictedAmount = request.amount + predictedDifference;
            if (isStoreStructure(request.target)) { // cap predicted amount at -1 * storeCapacity
                predictedAmount = Math.max(predictedAmount, -1 * request.target.storeCapacity);
            }
            else if (isEnergyStructure(request.target)) {
                predictedAmount = Math.min(predictedAmount, -1 * request.target.energyCapacity);
            }
            let resourceOutflux = _.sum(_.map(otherTargetingTransporters, other => other.carryCapacity - _.sum(other.carry)));
            predictedAmount = Math.min(predictedAmount + resourceOutflux, 0);
            return predictedAmount;
        }
    }
    // Functions for computing resource change rate ====================================================================
    /* Consider all possibilities of buffer structures to visit on the way to fulfilling the request */
    bufferChoices(transporter, request) {
        let [ticksUntilFree, newPos] = this.nextAvailability(transporter);
        let choices = [];
        let amount = this.predictedRequestAmount(transporter, request, [ticksUntilFree, newPos]);
        let carry;
        if (!transporter.task || transporter.task.target != request.target) {
            // If you are not targeting the requestor, use predicted carry after completing current task
            carry = this.predictedTransporterCarry(transporter);
        }
        else {
            // If you are targeting the requestor, use current carry for computations
            carry = transporter.carry;
        }
        if (amount > 0) { // requestInput instance, needs refilling
            if (request.resourceType == 'all') {
                log.warning(`Improper resourceType in bufferChoices! Type 'all' is only allowable for outputs!`);
                return [];
            }
            // Change in resources if transporter goes straight to the input
            let dQ_direct = Math.min(amount, carry[request.resourceType] || 0);
            // let dt_direct = Pathing.distance(newPos, request.target.pos) + ticksUntilFree;
            let dt_direct = ticksUntilFree + newPos.getMultiRoomRangeTo(request.target.pos)
                * LogisticsNetwork_1.settings.rangeToPathHeuristic;
            choices.push({
                dQ: dQ_direct,
                dt: dt_direct,
                targetRef: request.target.ref
            });
            if ((carry[request.resourceType] || 0) > amount || _.sum(carry) == transporter.carryCapacity) {
                return choices; // Return early if you already have enough resources to go direct or are already full
            }
            // Change in resources if transporter picks up resources from a buffer first
            for (let buffer of this.buffers) {
                let dQ_buffer = Math.min(amount, transporter.carryCapacity, buffer.store[request.resourceType] || 0);
                let dt_buffer = newPos.getMultiRoomRangeTo(buffer.pos) * LogisticsNetwork_1.settings.rangeToPathHeuristic
                    + Pathing.distance(buffer.pos, request.target.pos) + ticksUntilFree;
                choices.push({
                    dQ: dQ_buffer,
                    dt: dt_buffer,
                    targetRef: buffer.ref
                });
            }
        }
        else if (amount < 0) { // requestOutput instance, needs pickup
            // Change in resources if transporter goes straight to the output
            let remainingCarryCapacity = transporter.carryCapacity - _.sum(carry);
            let dQ_direct = Math.min(Math.abs(amount), remainingCarryCapacity);
            let dt_direct = newPos.getMultiRoomRangeTo(request.target.pos)
                * LogisticsNetwork_1.settings.rangeToPathHeuristic + ticksUntilFree;
            choices.push({
                dQ: dQ_direct,
                dt: dt_direct,
                targetRef: request.target.ref
            });
            if (remainingCarryCapacity >= Math.abs(amount) || remainingCarryCapacity == transporter.carryCapacity) {
                return choices; // Return early you have sufficient free space or are empty
            }
            // Change in resources if transporter drops off resources at a buffer first
            for (let buffer of this.buffers) {
                let dQ_buffer = Math.min(Math.abs(amount), transporter.carryCapacity, buffer.storeCapacity - _.sum(buffer.store));
                let dt_buffer = newPos.getMultiRoomRangeTo(buffer.pos) * LogisticsNetwork_1.settings.rangeToPathHeuristic
                    + Pathing.distance(buffer.pos, request.target.pos) + ticksUntilFree;
                choices.push({
                    dQ: dQ_buffer,
                    dt: dt_buffer,
                    targetRef: buffer.ref
                });
            }
            // if (store.resourceType == RESOURCE_ENERGY) {
            // 	// Only for when you're picking up more energy: check to see if you can put to available links
            // 	for (let link of this.colony.dropoffLinks) {
            // 		let linkDeltaResource = Math.min(Math.abs(amount), transporter.carryCapacity,
            // 			2 * link.energyCapacity);
            // 		let ticksUntilDropoff = Math.max(Pathing.distance(newPos, link.pos),
            // 										 this.colony.linkNetwork.getDropoffAvailability(link));
            // 		let linkDistance = ticksUntilDropoff +
            // 						   Pathing.distance(link.pos, store.target.pos) + ticksUntilFree;
            // 		choices.push({
            // 						 deltaResource: linkDeltaResource,
            // 						 deltaTicks   : linkDistance,
            // 						 targetRef    : link.ref
            // 					 });
            // 	}
            // }
        }
        return choices;
    }
    /* Compute the best possible value of |dResource / dt| */
    resourceChangeRate(transporter, request) {
        if (!this.cache.resourceChangeRate[request.id]) {
            this.cache.resourceChangeRate[request.id] = {};
        }
        if (!this.cache.resourceChangeRate[request.id][transporter.name]) {
            let choices = this.bufferChoices(transporter, request);
            let dQ_dt = _.map(choices, choice => request.multiplier * choice.dQ / Math.max(choice.dt, 0.1));
            this.cache.resourceChangeRate[request.id][transporter.name] = _.max(dQ_dt);
        }
        return this.cache.resourceChangeRate[request.id][transporter.name];
    }
    /* Generate requestor preferences in terms of transporters */
    requestPreferences(request, transporters) {
        // Requestors priortize transporters by change in resources per tick until pickup/delivery
        return _.sortBy(transporters, transporter => -1 * this.resourceChangeRate(transporter, request)); // -1 -> desc
    }
    /* Generate transporter preferences in terms of store structures */
    transporterPreferences(transporter) {
        // Transporters prioritize requestors by change in resources per tick until pickup/delivery
        return _.sortBy(this.requests, request => -1 * this.resourceChangeRate(transporter, request)); // -1 -> desc
    }
    /* Invalidates relevant portions of the cache once a transporter is assigned to a task */
    invalidateCache(transporter, request) {
        delete this.cache.nextAvailability[transporter.name];
        delete this.cache.predictedTransporterCarry[transporter.name];
        delete this.cache.resourceChangeRate[request.id][transporter.name];
    }
    /* Logs the output of the stable matching result */
    summarizeMatching() {
        let requests = this.requests.slice();
        let transporters = _.filter(this.colony.getCreepsByRole(Roles.transport), creep => !creep.spawning);
        let unmatchedTransporters = _.remove(transporters, transporter => !_.keys(this._matching).includes(transporter.name));
        let unmatchedRequests = _.remove(requests, request => !_.values(this._matching).includes(request));
        console.log(`Stable matching for ${this.colony.name} at ${Game.time}`);
        for (let transporter of transporters) {
            let transporterStr = transporter.name + ' ' + transporter.pos;
            let request = this._matching[transporter.name];
            let requestStr = request.target.ref + ' ' + request.target.pos.print;
            console.log(`${transporterStr.padRight(30)} : ${requestStr}`);
        }
        for (let transporter of unmatchedTransporters) {
            let transporterStr = transporter.name + ' ' + transporter.pos;
            console.log(`${transporterStr.padRight(30)} : ${''}`);
        }
        for (let request of unmatchedRequests) {
            let requestStr = request.target.ref + ' ' + request.target.pos;
            console.log(`${''.padRight(30)} : ${requestStr}`);
        }
        console.log();
    }
    /* Logs the current state of the logistics group to the console; useful for debugging */
    summarize() {
        // console.log(`Summary of logistics group for ${this.colony.name} at time ${Game.time}`);
        let info = [];
        for (let request of this.requests) {
            let targetType;
            if (request.target instanceof Resource) {
                targetType = 'resource';
            }
            else if (request.target instanceof Tombstone) {
                targetType = 'tombstone';
            }
            else {
                targetType = request.target.structureType;
            }
            let amount = 0;
            if (isResource(request.target)) {
                amount = request.target.amount;
            }
            else {
                if (request.resourceType == 'all') {
                    if (isTombstone(request.target) || isStoreStructure(request.target)) {
                        amount = _.sum(request.target.store);
                    }
                    else if (isEnergyStructure(request.target)) {
                        amount = -0.001;
                    }
                }
                else {
                    if (isTombstone(request.target) || isStoreStructure(request.target)) {
                        amount = request.target.store[request.resourceType] || 0;
                    }
                    else if (isEnergyStructure(request.target)) {
                        amount = request.target.energy;
                    }
                }
            }
            let targetingTprtrNames = _.map(LogisticsNetwork_1.targetingTransporters(request.target), c => c.name);
            info.push({
                target: targetType,
                resourceType: request.resourceType,
                requestAmount: request.amount,
                currentAmount: amount,
                targetedBy: targetingTprtrNames,
                pos: request.target.pos.print,
            });
        }
        console.log('Requests: \n' + columnify(info) + '\n');
        info = [];
        for (let transporter of this.colony.overlords.logistics.transporters) {
            let task = transporter.task ? transporter.task.name : 'none';
            let target = transporter.task ?
                transporter.task.proto._target.ref + ' ' + transporter.task.targetPos.printPlain : 'none';
            let nextAvailability = this.nextAvailability(transporter);
            info.push({
                creep: transporter.name,
                pos: transporter.pos.printPlain,
                task: task,
                target: target,
                availability: `available in ${nextAvailability[0]} ticks at ${nextAvailability[1].print}`,
            });
        }
        console.log('Transporters: \n' + columnify(info) + '\n');
    }
    get matching() {
        if (!this._matching) {
            this._matching = this.stableMatching(this.colony.overlords.logistics.transporters);
        }
        return this._matching;
    }
    /* Generate a stable matching of transporters to requests with Gale-Shapley algorithm */
    stableMatching(transporters) {
        let tPrefs = {};
        for (let transporter of transporters) {
            tPrefs[transporter.name] = _.map(this.transporterPreferences(transporter), request => request.id);
        }
        let rPrefs = {};
        for (let request of this.requests) {
            rPrefs[request.id] = _.map(this.requestPreferences(request, transporters), transporter => transporter.name);
        }
        let stableMatching = new Matcher(tPrefs, rPrefs).match();
        let requestMatch = _.mapValues(stableMatching, reqID => _.find(this.requests, request => request.id == reqID));
        return requestMatch;
    }
};
LogisticsNetwork.settings = {
    flagDropAmount: 1000,
    rangeToPathHeuristic: 1.1,
    carryThreshold: 800,
    droppedEnergyThreshold: 200,
};
LogisticsNetwork = LogisticsNetwork_1 = __decorate([
    profile
], LogisticsNetwork);

let TransportOverlord = class TransportOverlord extends Overlord {
    constructor(colony, priority = OverlordPriority.ownedRoom.transport) {
        super(colony, 'logistics', priority);
        this.transporters = this.zerg(Roles.transport);
    }
    neededTransportPower() {
        if (!this.colony.storage
            && !(this.colony.hatchery && this.colony.hatchery.battery)
            && !this.colony.upgradeSite.battery) {
            return 0;
        }
        let transportPower = 0;
        const scaling = 2; // this.colony.stage == ColonyStage.Larva ? 1.5 : 2.0; // aggregate round-trip multiplier
        // Add contributions to transport power from hauling energy from mining sites
        for (let flagName in this.colony.miningSites) {
            const o = this.colony.miningSites[flagName].overlords.mine;
            if (!o.isSuspended && o.miners.length > 0) {
                // Only count sites which have a container output and which have at least one miner present
                // (this helps in difficult "rebooting" situations)
                if ((o.container && !o.link) || o.allowDropMining) {
                    transportPower += o.energyPerTick * scaling * o.distance;
                }
            }
        }
        // Add transport power needed to move to upgradeSite
        if (this.colony.upgradeSite.battery) {
            transportPower += UPGRADE_CONTROLLER_POWER * this.colony.upgradeSite.upgradePowerNeeded * scaling *
                Pathing.distance(this.colony.pos, this.colony.upgradeSite.battery.pos);
        }
        if (this.colony.lowPowerMode) {
            // Reduce needed transporters when colony is in low power mode
            transportPower *= 0.5;
        }
        return transportPower / CARRY_CAPACITY;
    }
    init() {
        const ROAD_COVERAGE_THRESHOLD = 0.75; // switch from 1:1 to 2:1 transporters above this coverage threshold
        let setup = this.colony.roomPlanner.roadPlanner.roadCoverage < ROAD_COVERAGE_THRESHOLD
            ? Setups.transporters.early : Setups.transporters.default;
        let transportPowerEach = setup.getBodyPotential(CARRY, this.colony);
        let neededTransportPower = this.neededTransportPower();
        let numTransporters = Math.ceil(neededTransportPower / transportPowerEach);
        if (this.transporters.length == 0) {
            this.wishlist(numTransporters, setup, { priority: OverlordPriority.ownedRoom.firstTransport });
        }
        else {
            this.wishlist(numTransporters, setup);
        }
    }
    handleTransporter(transporter, request) {
        if (request) {
            let choices = this.colony.logisticsNetwork.bufferChoices(transporter, request);
            let bestChoice = _.last(_.sortBy(choices, choice => request.multiplier * choice.dQ
                / Math.max(choice.dt, 0.1)));
            let task = null;
            let amount = this.colony.logisticsNetwork.predictedRequestAmount(transporter, request);
            // Target is requesting input
            if (amount > 0) {
                if (isResource(request.target) || isTombstone(request.target)) {
                    log.warning(`Improper logistics request: should not request input for resource or tombstone!`);
                    return;
                }
                else if (request.resourceType == 'all') {
                    log.error(`${this.print}: cannot request 'all' as input!`);
                    return;
                }
                else {
                    task = Tasks.transfer(request.target, request.resourceType);
                }
                if (bestChoice.targetRef != request.target.ref) {
                    // If we need to go to a buffer first to get more stuff
                    let buffer = deref(bestChoice.targetRef);
                    let withdrawAmount = Math.min(buffer.store[request.resourceType] || 0, transporter.carryCapacity - _.sum(transporter.carry), amount);
                    task = task.fork(Tasks.withdraw(buffer, request.resourceType, withdrawAmount));
                    if (transporter.hasMineralsInCarry && request.resourceType == RESOURCE_ENERGY) {
                        task = task.fork(Tasks.transferAll(buffer));
                    }
                }
            }
            // Target is requesting output
            else if (amount < 0) {
                if (isResource(request.target)) {
                    task = Tasks.pickup(request.target);
                }
                else {
                    if (request.resourceType == 'all') {
                        if (!isStoreStructure(request.target) && !isTombstone(request.target)) {
                            log.error(`TransportOverlord: ` + ALL_RESOURCE_TYPE_ERROR);
                            return;
                        }
                        task = Tasks.withdrawAll(request.target);
                    }
                    else {
                        task = Tasks.withdraw(request.target, request.resourceType);
                    }
                }
                if (task && bestChoice.targetRef != request.target.ref) {
                    // If we need to go to a buffer first to deposit stuff
                    let buffer = deref(bestChoice.targetRef);
                    task = task.fork(Tasks.transferAll(buffer));
                }
            }
            else {
                // console.log(`${transporter.name} chooses a store with 0 amount!`);
                transporter.park();
            }
            // Assign the task to the transporter
            transporter.task = task;
            this.colony.logisticsNetwork.invalidateCache(transporter, request);
        }
        else {
            // If nothing to do, put everything in a store structure
            if (_.sum(transporter.carry) > 0) {
                if (transporter.hasMineralsInCarry) {
                    let target = this.colony.terminal || this.colony.storage;
                    if (target) {
                        transporter.task = Tasks.transferAll(target);
                    }
                }
                else {
                    let dropoffPoints = _.compact([this.colony.storage]); //, ...this.colony.dropoffLinks]);
                    // let bestDropoffPoint = minBy(dropoffPoints, function(dropoff: StructureLink | StructureStorage) {
                    // 	let range = transporter.pos.getMultiRoomRangeTo(dropoff.pos);
                    // 	if (dropoff instanceof StructureLink) {
                    // 		return Math.max(range, this.colony.linkNetwork.getDropoffAvailability(dropoff));
                    // 	} else {
                    // 		return range;
                    // 	}
                    // });
                    let bestDropoffPoint = transporter.pos.findClosestByMultiRoomRange(dropoffPoints);
                    if (bestDropoffPoint)
                        transporter.task = Tasks.transfer(bestDropoffPoint);
                }
            }
            else {
                let parkingSpot = transporter.pos;
                if (this.colony.storage) {
                    parkingSpot = this.colony.storage.pos;
                }
                else if (this.colony.roomPlanner.storagePos) {
                    parkingSpot = this.colony.roomPlanner.storagePos;
                }
                transporter.park(parkingSpot);
            }
        }
        //console.log(JSON.stringify(transporter.memory.task));
    }
    handleBigTransporter(bigTransporter) {
        let bestRequestViaStableMatching = this.colony.logisticsNetwork.matching[bigTransporter.name];
        this.handleTransporter(bigTransporter, bestRequestViaStableMatching);
    }
    /* Handles small transporters, which don't do well with the logisticsNetwork's stable matching system */
    handleSmolTransporter(smolTransporter) {
        // Just perform a single-sided greedy selection of all requests
        let bestRequestViaGreedy = _.first(this.colony.logisticsNetwork.transporterPreferences(smolTransporter));
        this.handleTransporter(smolTransporter, bestRequestViaGreedy);
    }
    pickupDroppedResources(transporter) {
        let droppedResource = transporter.pos.lookFor(LOOK_RESOURCES)[0];
        if (droppedResource) {
            transporter.pickup(droppedResource);
            return;
        }
        let tombstone = transporter.pos.lookFor(LOOK_TOMBSTONES)[0];
        if (tombstone) {
            let resourceType = _.last(_.sortBy(_.keys(tombstone.store), resourceType => (tombstone.store[resourceType] || 0)));
            transporter.withdraw(tombstone, resourceType);
        }
    }
    run() {
        this.autoRun(this.transporters, transporter => this.handleSmolTransporter(transporter));
    }
};
TransportOverlord = __decorate([
    profile
], TransportOverlord);

// Compute a hash of a block of code and register with Overmind
function assimilationLocked(code) {
    Assimilator.validate(code);
}

var TraderJoe_1;
const TraderMemoryDefaults = {
    cache: {
        sell: {},
        buy: {},
        tick: 0,
    },
    equalizeIndex: 0
};
const TraderStatsDefaults = {
    credits: 0,
    bought: {},
    sold: {},
};
// Maximum prices I'm willing to pay to buy various resources - based on shard2 market data in June 2018
// (might not always be up to date)
const maxMarketPrices = {
    default: 5.0,
    [RESOURCE_HYDROGEN]: 0.3,
    [RESOURCE_OXYGEN]: 0.25,
    [RESOURCE_UTRIUM]: 0.3,
    [RESOURCE_LEMERGIUM]: 0.25,
    [RESOURCE_KEANIUM]: 0.25,
    [RESOURCE_ZYNTHIUM]: 0.25,
    [RESOURCE_CATALYST]: 0.5,
};
const MAX_ENERGY_SELL_ORDERS = 5;
let TraderJoe = TraderJoe_1 = class TraderJoe {
    constructor() {
        this.memory = Mem.wrap(Memory.Overmind, 'trader', TraderMemoryDefaults, true);
        this.stats = Mem.wrap(Memory.stats.persistent, 'trader', TraderStatsDefaults);
        this.notifications = [];
    }
    refresh() {
        this.memory = Mem.wrap(Memory.Overmind, 'trader', TraderMemoryDefaults, true);
        this.stats = Mem.wrap(Memory.stats.persistent, 'trader', TraderStatsDefaults);
        this.notifications = [];
    }
    notify(msg) {
        this.notifications.push(bullet + msg);
    }
    /* Builds a cache for market - this is very expensive; use infrequently */
    buildMarketCache(verbose = false) {
        this.invalidateMarketCache();
        let myActiveOrderIDs = _.map(_.filter(Game.market.orders, order => order.active), order => order.id);
        let allOrders = Game.market.getAllOrders(order => !myActiveOrderIDs.includes(order.id) &&
            order.amount >= 1000); // don't include tiny orders in costs
        let groupedBuyOrders = _.groupBy(_.filter(allOrders, o => o.type == ORDER_BUY), o => o.resourceType);
        let groupedSellOrders = _.groupBy(_.filter(allOrders, o => o.type == ORDER_SELL), o => o.resourceType);
        for (let resourceType in groupedBuyOrders) {
            // Store buy order with maximum price in cache
            let prices = _.map(groupedBuyOrders[resourceType], o => o.price);
            let high = _.max(prices);
            let low = _.min(prices);
            if (verbose)
                console.log(`${resourceType} BUY: high: ${high}  low: ${low}`);
            // this.memory.cache.buy[resourceType] = minBy(groupedBuyOrders[resourceType], (o:Order) => -1 * o.price);
            this.memory.cache.buy[resourceType] = { high: high, low: low };
        }
        for (let resourceType in groupedSellOrders) {
            // Store sell order with minimum price in cache
            let prices = _.map(groupedSellOrders[resourceType], o => o.price);
            let high = _.max(prices);
            let low = _.min(prices);
            if (verbose)
                console.log(`${resourceType} SELL: high: ${high}  low: ${low}`);
            // this.memory.cache.sell[resourceType] = minBy(groupedSellOrders[resourceType], (o:Order) => o.price);
            this.memory.cache.sell[resourceType] = { high: high, low: low };
        }
        this.memory.cache.tick = Game.time;
    }
    invalidateMarketCache() {
        this.memory.cache = {
            sell: {},
            buy: {},
            tick: 0,
        };
    }
    /* Cost per unit including transfer price with energy converted to credits */
    effectivePrice(order, terminal) {
        if (order.roomName) {
            let transferCost = Game.market.calcTransactionCost(1000, order.roomName, terminal.room.name) / 1000;
            let energyToCreditMultiplier = 0.01; //this.cache.sell[RESOURCE_ENERGY] * 1.5;
            return order.price + transferCost * energyToCreditMultiplier;
        }
        else {
            return Infinity;
        }
    }
    /* Cost per unit for a buy order including transfer price with energy converted to credits */
    effectiveBuyPrice(order, terminal) {
        if (order.roomName) {
            let transferCost = Game.market.calcTransactionCost(1000, order.roomName, terminal.room.name) / 1000;
            let energyToCreditMultiplier = 0.01; //this.cache.sell[RESOURCE_ENERGY] * 1.5;
            return order.price - transferCost * energyToCreditMultiplier;
        }
        else {
            return Infinity;
        }
    }
    // private getBestOrder(mineralType: ResourceConstant, type: 'buy' | 'sell'): Order | undefined {
    // 	let cachedOrder = this.memory.cache[type][mineralType];
    // 	if (cachedOrder) {
    // 		let order = Game.market.getOrderById(cachedOrder.id);
    // 		if (order) {
    // 			// Update the order in memory
    // 			this.memory.cache[type][mineralType] = order;
    // 		}
    // 	}
    // }
    cleanUpInactiveOrders() {
        // Clean up sell orders that have expired or orders belonging to rooms no longer owned
        let ordersToClean = _.filter(Game.market.orders, o => (o.type == ORDER_SELL && o.active == false && o.remainingAmount == 0) // if order is expired, or
            || (Game.time - o.created > TraderJoe_1.settings.market.orders.timeout // order is old and almost done
                && o.remainingAmount < TraderJoe_1.settings.market.orders.cleanupAmount)
            || (o.roomName && !Overmind.colonies[o.roomName])); // order placed from dead colony
        for (let order of ordersToClean) {
            Game.market.cancelOrder(order.id);
        }
    }
    /* Opportunistically sells resources when the buy price is higher than current market sell low price*/
    lookForGoodDeals(terminal, resource, margin = 1.25) {
        if (Game.market.credits < TraderJoe_1.settings.market.reserveCredits) {
            return;
        }
        let amount = 5000;
        if (resource === RESOURCE_POWER) {
            amount = 100;
        }
        let ordersForMineral = Game.market.getAllOrders({ resourceType: resource, type: ORDER_BUY });
        ordersForMineral = _.filter(ordersForMineral, order => order.amount >= amount);
        if (ordersForMineral === undefined) {
            return;
        }
        let marketLow = this.memory.cache.sell[resource] ? this.memory.cache.sell[resource].low : undefined;
        if (marketLow == undefined) {
            return;
        }
        let order = maxBy(ordersForMineral, order => this.effectiveBuyPrice(order, terminal));
        if (order && order.price > marketLow * margin) {
            let amount = Math.min(order.amount, 10000);
            let cost = Game.market.calcTransactionCost(amount, terminal.room.name, order.roomName);
            if (terminal.store[RESOURCE_ENERGY] > cost) {
                let response = Game.market.deal(order.id, amount, terminal.room.name);
                this.logTransaction(order, terminal.room.name, amount, response);
            }
        }
    }
    buy(terminal, resource, amount) {
        if (Game.market.credits < TraderJoe_1.settings.market.reserveCredits || terminal.cooldown > 0) {
            return;
        }
        amount = Math.max(amount, TERMINAL_MIN_SEND);
        if (terminal.store[RESOURCE_ENERGY] < 10000 || terminal.storeCapacity - _.sum(terminal.store) < amount) {
            return;
        }
        let ordersForMineral = Game.market.getAllOrders({ resourceType: resource, type: ORDER_SELL });
        ordersForMineral = _.filter(ordersForMineral, order => order.amount >= amount);
        let bestOrder = minBy(ordersForMineral, (order) => order.price);
        let maxPrice = maxMarketPrices[resource] || maxMarketPrices.default;
        if (!onPublicServer()) {
            maxPrice = Infinity; // don't care about price limits if on private server
        }
        if (bestOrder && bestOrder.price <= maxPrice) {
            let response = Game.market.deal(bestOrder.id, amount, terminal.room.name);
            this.logTransaction(bestOrder, terminal.room.name, amount, response);
        }
    }
    sell(terminal, resource, amount = 10000) {
        if (Game.market.credits < TraderJoe_1.settings.market.reserveCredits) {
            return this.sellDirectly(terminal, resource, amount);
        }
        else {
            this.maintainSellOrder(terminal, resource, amount);
        }
    }
    /* Sell resources directly to a buyer rather than making a sell order */
    sellDirectly(terminal, resource, amount = 1000, flexibleAmount = true) {
        // If flexibleAmount is allowed, consider selling to orders which don't need the full amount
        let minAmount = flexibleAmount ? TERMINAL_MIN_SEND : amount;
        let ordersForMineral = Game.market.getAllOrders({ resourceType: resource, type: ORDER_BUY });
        ordersForMineral = _.filter(ordersForMineral, order => order.amount >= minAmount);
        let order = maxBy(ordersForMineral, order => this.effectiveBuyPrice(order, terminal));
        if (order) {
            let sellAmount = Math.min(order.amount, amount);
            let cost = Game.market.calcTransactionCost(sellAmount, terminal.room.name, order.roomName);
            if (terminal.store[RESOURCE_ENERGY] > cost) {
                let response = Game.market.deal(order.id, sellAmount, terminal.room.name);
                this.logTransaction(order, terminal.room.name, amount, response);
                return response;
            }
        }
    }
    /* Create or maintain a sell order */
    maintainSellOrder(terminal, resource, amount = 10000) {
        let marketLow = this.memory.cache.sell[resource] ? this.memory.cache.sell[resource].low : undefined;
        if (!marketLow) {
            return;
        }
        let mySellOrders = _.filter(Game.market.orders, o => o.type == ORDER_SELL &&
            o.resourceType == resource &&
            o.roomName == terminal.room.name);
        if (mySellOrders.length > 0) {
            for (let order of mySellOrders) {
                if (order.price > marketLow || (order.price < marketLow && order.remainingAmount == 0)) {
                    let ret = Game.market.changeOrderPrice(order.id, marketLow);
                    this.notify(`${terminal.room.print}: updating sell order price for ${resource} from ` +
                        `${order.price} to ${marketLow}. Response: ${ret}`);
                }
                if (order.remainingAmount < 2000) {
                    let addAmount = (amount - order.remainingAmount);
                    let ret = Game.market.extendOrder(order.id, addAmount);
                    this.notify(`${terminal.room.print}: extending sell order for ${resource} by ${addAmount}.` +
                        ` Response: ${ret}`);
                }
            }
        }
        else {
            let ret = Game.market.createOrder(ORDER_SELL, resource, marketLow, amount, terminal.room.name);
            this.notify(`${terminal.room.print}: creating sell order for ${resource} at price ${marketLow}. ` +
                `Response: ${ret}`);
        }
    }
    priceOf(mineralType) {
        if (this.memory.cache.sell[mineralType]) {
            return this.memory.cache.sell[mineralType].low;
        }
        else {
            return Infinity;
        }
    }
    logTransaction(order, terminalRoomName, amount, response) {
        let action = order.type == ORDER_SELL ? 'BOUGHT ' : 'SOLD   ';
        let cost = (order.price * amount).toFixed(2);
        let fee = order.roomName ? Game.market.calcTransactionCost(amount, order.roomName, terminalRoomName) : 0;
        let roomName = Game.rooms[terminalRoomName] ? Game.rooms[terminalRoomName].print : terminalRoomName;
        let msg;
        if (order.type == ORDER_SELL) {
            msg = `${roomName} ${leftArrow} ${amount} ${order.resourceType} ${leftArrow} ` +
                `${printRoomName(order.roomName)} (result: ${response})`;
        }
        else {
            msg = `${roomName} ${rightArrow} ${amount} ${order.resourceType} ${rightArrow} ` +
                `${printRoomName(order.roomName)} (result: ${response})`;
        }
        this.notify(msg);
    }
    // Look through transactions happening on the previous tick and record stats
    recordStats() {
        this.stats.credits = Game.market.credits;
        const time = Game.time - 1;
        // Incoming transactions
        for (let transaction of Game.market.incomingTransactions) {
            if (transaction.time < time) {
                break; // only look at things from last tick
            }
            else {
                if (transaction.order) {
                    const resourceType = transaction.resourceType;
                    const amount = transaction.amount;
                    const price = transaction.order.price;
                    if (!this.stats.bought[resourceType]) {
                        this.stats.bought[resourceType] = { amount: 0, credits: 0 };
                    }
                    this.stats.bought[resourceType].amount += amount;
                    this.stats.bought[resourceType].credits += amount * price;
                }
            }
        }
        // Outgoing transactions
        for (let transaction of Game.market.outgoingTransactions) {
            if (transaction.time < time) {
                break; // only look at things from last tick
            }
            else {
                if (transaction.order) {
                    const resourceType = transaction.resourceType;
                    const amount = transaction.amount;
                    const price = transaction.order.price;
                    if (!this.stats.sold[resourceType]) {
                        this.stats.sold[resourceType] = { amount: 0, credits: 0 };
                    }
                    this.stats.sold[resourceType].amount += amount;
                    this.stats.sold[resourceType].credits += amount * price;
                }
            }
        }
    }
    init() {
        if (Game.time - (this.memory.cache.tick || 0) > TraderJoe_1.settings.cache.timeout) {
            this.buildMarketCache();
        }
    }
    run() {
        if (Game.time % 10 == 0) {
            this.cleanUpInactiveOrders();
        }
        if (this.notifications.length > 0) {
            log.info(`Trade network activity: ` + alignedNewline + this.notifications.join(alignedNewline));
        }
        this.recordStats();
    }
};
TraderJoe.settings = {
    cache: {
        timeout: 25,
    },
    market: {
        reserveCredits: 10000,
        boostCredits: 15000,
        orders: {
            timeout: 100000,
            cleanupAmount: 10,
        }
    },
};
TraderJoe = TraderJoe_1 = __decorate([
    profile,
    assimilationLocked
], TraderJoe);

// Abathur is responsible for the evolution of the swarm and directs global production of minerals
var Abathur_1;
const priorityStockAmounts = {
    XGHO2: 1000,
    XLHO2: 1000,
    XZHO2: 1000,
    XZH2O: 1000,
    XKHO2: 1000,
    XUH2O: 1000,
    GHO2: 1000,
    LHO2: 1000,
    ZHO2: 1000,
    ZH2O: 1000,
    UH2O: 1000,
    KHO2: 1000,
    GO: 1000,
    LO: 1000,
    ZO: 1000,
    ZH: 1000,
    UH: 1000,
    KO: 1000,
};
const wantedStockAmounts = {
    UH: 3000,
    KO: 3000,
    XGHO2: 10000,
    XLHO2: 10000,
    XZHO2: 6000,
    XZH2O: 6000,
    XKHO2: 8000,
    XUH2O: 8000,
    G: 5000,
    XLH2O: 3000,
    LH: 3000,
    XUHO2: 3000,
    XKH2O: 3000,
    XGH2O: 12000 // For upgraders
};
const baseStockAmounts = {
    [RESOURCE_CATALYST]: 5000,
    [RESOURCE_ZYNTHIUM]: 5000,
    [RESOURCE_LEMERGIUM]: 5000,
    [RESOURCE_KEANIUM]: 5000,
    [RESOURCE_UTRIUM]: 5000,
    [RESOURCE_OXYGEN]: 5000,
    [RESOURCE_HYDROGEN]: 5000
};
// Compute priority and wanted stock
let _priorityStock = [];
for (let resourceType in priorityStockAmounts) {
    let stock = {
        mineralType: resourceType,
        amount: priorityStockAmounts[resourceType]
    };
    _priorityStock.push(stock);
}
let _wantedStock = [];
for (let resourceType in wantedStockAmounts) {
    let stock = {
        mineralType: resourceType,
        amount: wantedStockAmounts[resourceType]
    };
    _wantedStock.push(stock);
}
const priorityStock = _priorityStock;
const wantedStock = _wantedStock;
const AbathurMemoryDefaults = {
    sleepUntil: 0
};
let Abathur = Abathur_1 = class Abathur {
    constructor(colony) {
        this.colony = colony;
        this.memory = Mem.wrap(this.colony.memory, 'abathur', AbathurMemoryDefaults);
        this.priorityStock = priorityStock;
        this.wantedStock = wantedStock;
        this.assets = colony.assets;
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'abathur', AbathurMemoryDefaults);
        this.assets = this.colony.assets;
    }
    /* Summarizes the total of all resources currently in a colony store structure */
    computeGlobalAssets() {
        let colonyAssets = [];
        for (let colony of getAllColonies()) {
            colonyAssets.push(colony.assets);
        }
        return mergeSum(colonyAssets);
    }
    get globalAssets() {
        if (!this._globalAssets) {
            this._globalAssets = this.computeGlobalAssets();
        }
        return this._globalAssets;
    }
    canReceiveBasicMineralsForReaction(mineralQuantities, amount) {
        for (let mineral in mineralQuantities) {
            if (!this.someColonyHasExcess(mineral, mineralQuantities[mineral])) {
                return false;
            }
        }
        return true;
    }
    canBuyBasicMineralsForReaction(mineralQuantities) {
        if (Game.market.credits < TraderJoe.settings.market.reserveCredits) {
            return false;
        }
        for (let mineral in mineralQuantities) {
            let maxPrice = maxMarketPrices[mineral] || maxMarketPrices.default;
            if (!onPublicServer()) {
                maxPrice = Infinity;
            }
            if (Overmind.tradeNetwork.priceOf(mineral) > maxPrice) {
                return false;
            }
        }
        return true;
    }
    hasExcess(mineralType, excessAmount = 0) {
        return this.assets[mineralType] - excessAmount > Math.max((wantedStockAmounts[mineralType] || 0), (priorityStockAmounts[mineralType] || 0));
    }
    someColonyHasExcess(mineralType, excessAmount = 0) {
        return _.any(getAllColonies(), colony => colony.abathur.hasExcess(mineralType, excessAmount));
    }
    /* Generate a queue of reactions to produce the most needed compound */
    getReactionQueue(verbose = false) {
        // Return nothing if you are sleeping; prevents wasteful reaction queue calculations
        if (Game.time < this.memory.sleepUntil) {
            return [];
        }
        // Compute the reaction queue for the highest priority item that you should be and can be making
        let stocksToCheck = [priorityStockAmounts, wantedStockAmounts];
        for (let stocks of stocksToCheck) {
            for (let resourceType in stocks) {
                let amountOwned = this.assets[resourceType] || 0;
                let amountNeeded = stocks[resourceType];
                if (amountOwned < amountNeeded) { // if there is a shortage of this resource
                    let reactionQueue = this.buildReactionQueue(resourceType, amountNeeded - amountOwned, verbose);
                    let missingBaseMinerals = this.getMissingBasicMinerals(reactionQueue);
                    if (!_.any(missingBaseMinerals)
                        || this.canReceiveBasicMineralsForReaction(missingBaseMinerals, amountNeeded + 1000)
                        || this.canBuyBasicMineralsForReaction(missingBaseMinerals)) {
                        return reactionQueue;
                    }
                }
            }
        }
        // If there's nothing you can make, sleep for 100 ticks
        this.memory.sleepUntil = Game.time + Abathur_1.settings.sleepTime;
        return [];
    }
    /* Build a reaction queue for a target compound */
    buildReactionQueue(mineral, amount, verbose = false) {
        amount = minMax(amount, Abathur_1.settings.minBatchSize, Abathur_1.settings.maxBatchSize);
        if (verbose)
            console.log(`Abathur@${this.colony.room.print}: building reaction queue for ${amount} ${mineral}`);
        let reactionQueue = [];
        for (let ingredient of this.ingredientsList(mineral)) {
            let productionAmount = amount;
            if (ingredient != mineral) {
                if (verbose)
                    console.log(`productionAmount: ${productionAmount}, assets: ${this.assets[ingredient]}`);
                productionAmount = Math.max(productionAmount - (this.assets[ingredient] || 0), 0);
            }
            productionAmount = Math.min(productionAmount, Abathur_1.settings.maxBatchSize);
            reactionQueue.push({ mineralType: ingredient, amount: productionAmount });
        }
        if (verbose)
            console.log(`Pre-trim queue: ${JSON.stringify(reactionQueue)}`);
        reactionQueue = this.trimReactionQueue(reactionQueue);
        if (verbose)
            console.log(`Post-trim queue: ${JSON.stringify(reactionQueue)}`);
        reactionQueue = _.filter(reactionQueue, rxn => rxn.amount > 0);
        if (verbose)
            console.log(`Final queue: ${JSON.stringify(reactionQueue)}`);
        return reactionQueue;
    }
    /* Trim a reaction queue, reducing the amounts of precursor compounds which need to be produced */
    trimReactionQueue(reactionQueue) {
        // Scan backwards through the queue and reduce the production amount of subsequently baser resources as needed
        reactionQueue.reverse();
        for (let reaction of reactionQueue) {
            let [ing1, ing2] = REAGENTS[reaction.mineralType];
            let precursor1 = _.findIndex(reactionQueue, rxn => rxn.mineralType == ing1);
            let precursor2 = _.findIndex(reactionQueue, rxn => rxn.mineralType == ing2);
            for (let index of [precursor1, precursor2]) {
                if (index != -1) {
                    if (reactionQueue[index].amount == 0) {
                        reactionQueue[index].amount = 0;
                    }
                    else {
                        reactionQueue[index].amount = minMax(reaction.amount, Abathur_1.settings.minBatchSize, reactionQueue[index].amount);
                    }
                }
            }
        }
        reactionQueue.reverse();
        return reactionQueue;
    }
    /* Figure out which basic minerals are missing and how much */
    getMissingBasicMinerals(reactionQueue) {
        let requiredBasicMinerals = this.getRequiredBasicMinerals(reactionQueue);
        let missingBasicMinerals = {};
        for (let mineralType in requiredBasicMinerals) {
            let amountMissing = requiredBasicMinerals[mineralType] - (this.assets[mineralType] || 0);
            if (amountMissing > 0) {
                missingBasicMinerals[mineralType] = amountMissing;
            }
        }
        return missingBasicMinerals;
    }
    /* Get the required amount of basic minerals for a reaction queue */
    getRequiredBasicMinerals(reactionQueue) {
        let requiredBasicMinerals = {
            [RESOURCE_HYDROGEN]: 0,
            [RESOURCE_OXYGEN]: 0,
            [RESOURCE_UTRIUM]: 0,
            [RESOURCE_KEANIUM]: 0,
            [RESOURCE_LEMERGIUM]: 0,
            [RESOURCE_ZYNTHIUM]: 0,
            [RESOURCE_CATALYST]: 0,
        };
        for (let reaction of reactionQueue) {
            let ingredients = REAGENTS[reaction.mineralType];
            for (let ingredient of ingredients) {
                if (!REAGENTS[ingredient]) { // resource is base mineral
                    requiredBasicMinerals[ingredient] += reaction.amount;
                }
            }
        }
        return requiredBasicMinerals;
    }
    /* Recursively generate a list of ingredients required to produce a compound */
    ingredientsList(mineral) {
        if (!REAGENTS[mineral] || _.isEmpty(mineral)) {
            return [];
        }
        else {
            return this.ingredientsList(REAGENTS[mineral][0])
                .concat(this.ingredientsList(REAGENTS[mineral][1]), mineral);
        }
    }
};
Abathur.settings = {
    minBatchSize: 100,
    maxBatchSize: 800,
    sleepTime: 100,
};
Abathur = Abathur_1 = __decorate([
    profile
], Abathur);

// Evolution chamber: manages lab boosting behavior
var EvolutionChamber_1;
const LabStatus = {
    Idle: 0,
    AcquiringMinerals: 1,
    LoadingLabs: 2,
    Synthesizing: 3,
    UnloadingLabs: 4,
};
const LabStageTimeouts = {
    Idle: Infinity,
    AcquiringMinerals: 100,
    LoadingLabs: 50,
    Synthesizing: 10000,
    UnloadingLabs: 1000
};
const LAB_USAGE_WINDOW = 100;
const EvolutionChamberMemoryDefaults = {
    status: LabStatus.Idle,
    statusTick: 0,
    activeReaction: undefined,
    reactionQueue: [],
    labMineralTypes: {},
    stats: {
        totalProduction: {},
        avgUsage: 1,
    }
};
function neighboringLabs(pos) {
    return _.compact(_.map(pos.neighbors, neighbor => neighbor.lookForStructure(STRUCTURE_LAB)));
}
function labsAreEmpty(labs) {
    return _.all(labs, lab => lab.mineralAmount == 0);
}
let EvolutionChamber = EvolutionChamber_1 = class EvolutionChamber extends HiveCluster {
    constructor(colony, terminal) {
        super(colony, terminal, 'evolutionChamber');
        this.memory = Mem.wrap(this.colony.memory, 'evolutionChamber', EvolutionChamberMemoryDefaults);
        // Register physical components
        this.terminal = terminal;
        this.terminalNetwork = Overmind.terminalNetwork;
        this.labs = colony.labs;
        // Reserve some easily-accessible labs which are restricted not to be reagent labs
        let restrictedLabs = this.colony.bunker ?
            _.filter(this.labs, lab => lab.pos.findInRange(this.colony.spawns, 1).length > 0) :
            _.take(_.sortBy(this.labs, lab => Pathing.distance(this.terminal.pos, lab.pos)), 1);
        // if (this.colony.bunker) {
        // 	this.boostingLabs = _.filter(this.labs, lab => lab.pos.findInRange(this.colony.spawns, 1).length > 0);
        // } else {
        // 	this.boostingLabs = [_.first(_.sortBy(this.labs, lab => Pathing.distance(this.terminal.pos, lab.pos)))];
        // }
        // Reagent labs are range=2 from all other labs and are not a boosting lab
        let range2Labs = _.filter(this.labs, lab => _.all(this.labs, otherLab => lab.pos.inRangeTo(otherLab, 2)));
        let reagentLabCandidates = _.filter(range2Labs, lab => !_.any(restrictedLabs, l => l.id == lab.id));
        if (this.colony.bunker && this.colony.labs.length == 10) {
            this.reagentLabs = _.take(_.sortBy(reagentLabCandidates, lab => -1 * lab.pos.findInRange(this.boostingLabs, 1).length), 2);
        }
        else {
            this.reagentLabs = _.take(_.sortBy(reagentLabCandidates, lab => -1 * neighboringLabs(lab.pos).length), 2);
        }
        // Product labs are everything that isn't a reagent lab. (boostingLab can also be a productLab)
        this.productLabs = _.difference(this.labs, this.reagentLabs);
        // Boosting labs are product labs sorted by distance to terminal
        let unrestrictedBoostingLabs = _.sortBy(_.difference(this.productLabs, restrictedLabs), lab => Pathing.distance(this.terminal.pos, lab.pos));
        this.boostingLabs = [...restrictedLabs, ...unrestrictedBoostingLabs];
        // This keeps track of reservations for boosting
        this.labReservations = {};
        // this.boostQueue = {};
        this.neededBoosts = {};
        if (this.colony.commandCenter && this.colony.layout == 'twoPart') {
            // in two-part layout, evolution chamber shares a common request group with command center
            this.transportRequests = this.colony.commandCenter.transportRequests;
        }
        else {
            // otherwise (in bunker layout), it uses colony/hatchery transport requests
            this.transportRequests = this.colony.transportRequests;
        }
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'evolutionChamber', EvolutionChamberMemoryDefaults);
        $.refreshRoom(this);
        $.refresh(this, 'terminal', 'labs', 'boostingLabs', 'reagentLabs', 'productLabs');
        this.labReservations = {};
        // this.boostQueue = {};
        this.neededBoosts = {};
    }
    spawnMoarOverlords() {
        // Evolution chamber is attended to by queens; overlord spawned at Hatchery
    }
    statusTimeoutCheck() {
        let ticksInStatus = Game.time - this.memory.statusTick;
        let timeout = false;
        switch (this.memory.status) {
            case LabStatus.Idle:
                timeout = ticksInStatus > LabStageTimeouts.Idle;
                break;
            case LabStatus.AcquiringMinerals:
                timeout = ticksInStatus > LabStageTimeouts.AcquiringMinerals;
                break;
            case LabStatus.LoadingLabs:
                timeout = ticksInStatus > LabStageTimeouts.LoadingLabs;
                break;
            case LabStatus.Synthesizing:
                timeout = ticksInStatus > LabStageTimeouts.Synthesizing;
                break;
            case LabStatus.UnloadingLabs:
                timeout = ticksInStatus > LabStageTimeouts.UnloadingLabs;
                break;
            default:
                log.warning(`Bad lab state at ${this.print}!`);
                this.memory.status = LabStatus.Idle;
                this.memory.statusTick = Game.time;
                break;
        }
        if (timeout) {
            log.warning(`${this.print}: stuck in state ${this.memory.status} for ${ticksInStatus} ticks, ` +
                `rebuilding reaction queue and reverting to idle state!`);
            this.memory.status = LabStatus.Idle;
            this.memory.statusTick = Game.time;
            this.memory.activeReaction = undefined;
            this.memory.reactionQueue = [];
        }
    }
    initLabStatus() {
        if (!this.memory.activeReaction && this.memory.status != LabStatus.Idle) {
            log.warning(`No active reaction at ${this.print}!`);
            this.memory.status = LabStatus.Idle;
        }
        switch (this.memory.status) {
            case LabStatus.Idle:
                if (this.memory.activeReaction) {
                    let [ing1, ing2] = REAGENTS[this.memory.activeReaction.mineralType];
                    log.info(`${this.colony.room.print}: starting synthesis of ${ing1} + ${ing2} ${rightArrow} ` +
                        this.memory.activeReaction.mineralType);
                    this.memory.status = LabStatus.AcquiringMinerals;
                    this.memory.statusTick = Game.time;
                }
                break;
            case LabStatus.AcquiringMinerals: // "We acquire more mineralzzz"
                let missingIngredients = this.colony.abathur.getMissingBasicMinerals([this.memory.activeReaction]);
                if (_.all(missingIngredients, amount => amount == 0)) {
                    // Loading labs if all minerals are present but labs not at desired capacity yet
                    this.memory.status = LabStatus.LoadingLabs;
                    this.memory.statusTick = Game.time;
                }
                break;
            case LabStatus.LoadingLabs:
                if (_.all(this.reagentLabs, lab => lab.mineralAmount >= this.memory.activeReaction.amount &&
                    REAGENTS[this.memory.activeReaction.mineralType]
                        .includes(lab.mineralType))) {
                    this.memory.status = LabStatus.Synthesizing;
                    this.memory.statusTick = Game.time;
                }
                break;
            case LabStatus.Synthesizing:
                if (_.any(this.reagentLabs, lab => lab.mineralAmount < LAB_REACTION_AMOUNT)) {
                    this.memory.status = LabStatus.UnloadingLabs;
                    this.memory.statusTick = Game.time;
                }
                break;
            case LabStatus.UnloadingLabs:
                if (_.all([...this.reagentLabs, ...this.productLabs], lab => lab.mineralAmount == 0)) {
                    this.memory.status = LabStatus.Idle;
                    this.memory.statusTick = Game.time;
                }
                break;
            default:
                log.warning(`Bad lab state at ${this.print}!`);
                this.memory.status = LabStatus.Idle;
                this.memory.statusTick = Game.time;
                break;
        }
        this.statusTimeoutCheck();
    }
    reagentLabRequests(reagentLabs) {
        if (this.memory.activeReaction) {
            let { mineralType, amount } = this.memory.activeReaction;
            let [ing1, ing2] = REAGENTS[mineralType];
            let [lab1, lab2] = reagentLabs;
            if (!lab1 || !lab2)
                return;
            // Empty out any incorrect minerals and request the correct reagents
            if (this.memory.status == LabStatus.UnloadingLabs || (lab1.mineralType != ing1 && lab1.mineralAmount > 0)) {
                this.transportRequests.requestOutput(lab1, Priority.Normal, { resourceType: lab1.mineralType });
            }
            else if (this.memory.status == LabStatus.LoadingLabs && lab1.mineralAmount < amount) {
                this.transportRequests.requestInput(lab1, Priority.Normal, {
                    resourceType: ing1,
                    amount: amount - lab1.mineralAmount,
                });
            }
            if (this.memory.status == LabStatus.UnloadingLabs || (lab2.mineralType != ing2 && lab2.mineralAmount > 0)) {
                this.transportRequests.requestOutput(lab2, Priority.Normal, { resourceType: lab2.mineralType });
            }
            else if (this.memory.status == LabStatus.LoadingLabs && lab2.mineralAmount < amount) {
                this.transportRequests.requestInput(lab2, Priority.Normal, {
                    resourceType: ing2,
                    amount: amount - lab2.mineralAmount,
                });
            }
        }
        else {
            // Labs should be empty when no reaction process is currently happening
            for (let lab of reagentLabs) {
                if (lab.mineralType && lab.mineralAmount > 0) {
                    this.transportRequests.requestOutput(lab, Priority.Normal, { resourceType: lab.mineralType });
                }
            }
        }
    }
    productLabRequests(labs) {
        if (this.memory.activeReaction) {
            let { mineralType, amount } = this.memory.activeReaction;
            for (let lab of labs) {
                let labHasWrongMineral = lab.mineralType != mineralType && lab.mineralAmount > 0;
                let labIsFull = lab.mineralAmount == lab.mineralCapacity;
                // Empty out incorrect minerals or if it's time to unload or if lab is full
                if ((this.memory.status == LabStatus.UnloadingLabs && lab.mineralAmount > 0) ||
                    labHasWrongMineral || labIsFull) {
                    this.transportRequests.requestOutput(lab, Priority.NormalLow, { resourceType: lab.mineralType });
                }
            }
        }
        else {
            // Labs should be empty when no reaction process is currently happening
            for (let lab of labs) {
                if (lab.mineralType && lab.mineralAmount > 0) {
                    this.transportRequests.requestOutput(lab, Priority.NormalLow, { resourceType: lab.mineralType });
                }
            }
        }
    }
    boosterLabRequests(labs) {
        for (let lab of labs) {
            let { mineralType, amount } = this.labReservations[lab.id];
            // Empty out incorrect minerals
            if (lab.mineralType != mineralType && lab.mineralAmount > 0) {
                this.transportRequests.requestOutput(lab, Priority.NormalHigh, { resourceType: lab.mineralType });
            }
            else {
                this.transportRequests.requestInput(lab, Priority.NormalHigh, {
                    resourceType: mineralType,
                    amount: amount - lab.mineralAmount
                });
            }
        }
    }
    registerRequests() {
        // Separate product labs into actively boosting or ready for reaction
        let boostingProductLabs = _.filter(this.productLabs, lab => this.labReservations[lab.id]);
        let reactionProductLabs = _.filter(this.productLabs, lab => !this.labReservations[lab.id]);
        // Handle energy requests for labs with different priorities
        let boostingRefillLabs = _.filter(boostingProductLabs, lab => lab.energy < lab.energyCapacity);
        _.forEach(boostingRefillLabs, lab => this.transportRequests.requestInput(lab, Priority.High));
        let reactionRefillLabs = _.filter(reactionProductLabs, lab => lab.energy < lab.energyCapacity);
        _.forEach(reactionRefillLabs, lab => this.transportRequests.requestInput(lab, Priority.NormalLow));
        let reagentRefillLabs = _.filter(this.reagentLabs, lab => lab.energy < lab.energyCapacity);
        _.forEach(reagentRefillLabs, lab => this.transportRequests.requestInput(lab, Priority.NormalLow));
        // Request resources delivered to / withdrawn from each type of lab
        this.reagentLabRequests(this.reagentLabs);
        this.productLabRequests(reactionProductLabs);
        this.boosterLabRequests(boostingProductLabs);
    }
    // Lab mineral reservations ========================================================================================
    /* Reserves a product lab for boosting with a compound unrelated to production */
    reserveLab(mineralType, amount, lab) {
        // _.remove(this.productLabs, productLab => productLab.id == lab.id);
        this.labReservations[lab.id] = { mineralType: mineralType, amount: amount };
    }
    /* Return the amount of a given resource necessary to fully boost a creep body */
    static requiredBoostAmount(body, boostType) {
        let existingBoostCounts = _.countBy(body, part => part.boost);
        let numPartsToBeBoosted = _.filter(body, part => part.type == boostParts[boostType]).length;
        return LAB_BOOST_MINERAL * (numPartsToBeBoosted - (existingBoostCounts[boostType] || 0));
    }
    /* Return whether you have the resources to fully boost a creep body with a given resource */
    canBoost(body, boostType) {
        let boostAmount = EvolutionChamber_1.requiredBoostAmount(body, boostType);
        if (this.colony.assets[boostType] >= boostAmount) {
            // Does this colony have the needed resources already?
            return true;
        }
        else if (this.terminalNetwork.assets[boostType] >= 2 * boostAmount) {
            // Is there enough of the resource in terminalNetwork?
            return true;
        }
        else {
            // Can you buy the resources on the market?
            return (Game.market.credits > TraderJoe.settings.market.boostCredits +
                boostAmount * Overmind.tradeNetwork.priceOf(boostType));
        }
    }
    /* Request boosts sufficient to fully boost a given creep to be added to the boosting queue */
    requestBoost(creep, boostType) {
        // Add the required amount to the neededBoosts
        let boostAmount = EvolutionChamber_1.requiredBoostAmount(creep.body, boostType);
        if (!this.neededBoosts[boostType]) {
            this.neededBoosts[boostType] = 0;
        }
        this.neededBoosts[boostType] = Math.min(this.neededBoosts[boostType] + boostAmount, LAB_MINERAL_CAPACITY);
    }
    // Initialization and operation ====================================================================================
    init() {
        // Get a reaction queue if needed
        if (this.memory.reactionQueue.length == 0) {
            this.memory.reactionQueue = this.colony.abathur.getReactionQueue();
        }
        // Switch to next reaction on the queue if you are idle
        if (this.memory.status == LabStatus.Idle) {
            this.memory.activeReaction = this.memory.reactionQueue.shift();
        }
        // Set boosting lab reservations and compute needed resources
        for (let mineralType in this.neededBoosts) {
            if (this.neededBoosts[mineralType] == 0)
                continue;
            let boostLab = undefined;
            for (let id in this.labReservations) { // find a lab already reserved for this mineral type
                if (this.labReservations[id] && this.labReservations[id].mineralType == mineralType) {
                    boostLab = deref(id);
                }
            }
            if (!boostLab) { // otherwise choose the first unreserved product lab
                boostLab = _.find(this.boostingLabs, lab => !this.labReservations[lab.id]);
            }
            if (boostLab) {
                this.reserveLab(mineralType, this.neededBoosts[mineralType], boostLab);
            }
        }
        this.initLabStatus();
        this.registerRequests();
    }
    run() {
        // Obtain resources for boosting
        for (let resourceType in this.neededBoosts) {
            let needAmount = Math.max(this.neededBoosts[resourceType] - (this.colony.assets[resourceType] || 0), 0);
            if (needAmount > 0) {
                this.terminalNetwork.requestResource(this.terminal, resourceType, needAmount, true, 0);
            }
        }
        // Obtain resources for reaction queue
        let queue = this.memory.reactionQueue;
        if (this.memory.activeReaction && this.memory.status == LabStatus.AcquiringMinerals) {
            queue = [this.memory.activeReaction].concat(queue);
        }
        let missingBasicMinerals = this.colony.abathur.getMissingBasicMinerals(queue);
        for (let resourceType in missingBasicMinerals) {
            if (missingBasicMinerals[resourceType] > 0) {
                this.terminalNetwork.requestResource(this.terminal, resourceType, missingBasicMinerals[resourceType], true);
            }
        }
        // Run the reactions
        if (this.memory.status == LabStatus.Synthesizing) {
            let [lab1, lab2] = this.reagentLabs;
            for (let lab of this.productLabs) {
                if (lab.cooldown == 0 && !this.labReservations[lab.id]) {
                    let result = lab.runReaction(lab1, lab2);
                    if (result == OK) { // update total production amount in memory
                        const product = this.memory.activeReaction ? this.memory.activeReaction.mineralType : 'ERROR';
                        if (!this.memory.stats.totalProduction[product]) {
                            this.memory.stats.totalProduction[product] = 0;
                        }
                        this.memory.stats.totalProduction[product] += LAB_REACTION_AMOUNT;
                    }
                    else {
                        log.debug(`Couldn't run reaction for lab @ ${lab.pos.print}! Result: ${result}`);
                    }
                }
            }
        }
        // Record stats
        this.stats();
    }
    drawLabReport(coord) {
        let { x, y } = coord;
        let height = 2;
        let titleCoords = Visualizer.section(`${this.colony.name} Evolution Chamber`, { x, y, roomName: this.room.name }, 9.5, height + .1);
        let boxX = titleCoords.x;
        y = titleCoords.y + 0.25;
        let status;
        switch (this.memory.status) {
            case LabStatus.Idle:
                status = 'IDLE';
                break;
            case LabStatus.AcquiringMinerals:
                status = 'acquire minerals';
                break;
            case LabStatus.LoadingLabs:
                status = 'loading labs';
                break;
            case LabStatus.Synthesizing:
                status = 'synthesizing';
                break;
            case LabStatus.UnloadingLabs:
                status = 'unloading labs';
                break;
            default:
                status = 'INVALID';
                break;
        }
        let activeReaction = this.memory.activeReaction;
        let mineral = activeReaction ? activeReaction.mineralType : 'NONE';
        Visualizer.text(`Status: ${status}`, { x: boxX, y: y, roomName: this.room.name });
        y += 1;
        if (this.memory.status == LabStatus.Synthesizing && activeReaction) {
            let amountDone = _.sum(_.map(this.productLabs, lab => lab.mineralType == activeReaction.mineralType ? lab.mineralAmount : 0));
            Visualizer.text(activeReaction.mineralType, { x: boxX, y: y, roomName: this.room.name });
            Visualizer.barGraph([amountDone, activeReaction.amount], { x: boxX + 4, y: y, roomName: this.room.name }, 5);
            y += 1;
        }
        else {
            Visualizer.text(`Active reaction: ${mineral}`, { x: boxX, y: y, roomName: this.room.name });
            y += 1;
        }
        return { x: x, y: y + .25 };
    }
    visuals(coord) {
        const vis = this.room.visual;
        // Lab visuals
        for (let lab of this.labs) {
            if (lab.mineralType) {
                vis.resource(lab.mineralType, lab.pos.x, lab.pos.y);
            }
        }
        // Draw lab report
        return this.drawLabReport(coord);
    }
    stats() {
        Stats.log(`colonies.${this.colony.name}.evolutionChamber.totalProduction`, this.memory.stats.totalProduction);
        let labUsage = _.sum(this.productLabs, lab => lab.cooldown > 0 ? 1 : 0) / this.productLabs.length;
        this.memory.stats.avgUsage = exponentialMovingAverage(labUsage, this.memory.stats.avgUsage, LAB_USAGE_WINDOW);
        Stats.log(`colonies.${this.colony.name}.evolutionChamber.avgUsage`, this.memory.stats.avgUsage);
    }
};
EvolutionChamber.settings = {};
EvolutionChamber = EvolutionChamber_1 = __decorate([
    profile
], EvolutionChamber);

const DEFAULT_NUM_SCOUTS = 3;
let RandomWalkerScoutOverlord = class RandomWalkerScoutOverlord extends Overlord {
    constructor(colony, priority = OverlordPriority.scouting.randomWalker) {
        super(colony, 'scout', priority);
        this.scouts = this.zerg(Roles.scout, { notifyWhenAttacked: false });
    }
    init() {
        this.wishlist(DEFAULT_NUM_SCOUTS, Setups.scout);
    }
    handleScout(scout) {
        // Stomp on enemy construction sites
        let enemyConstructionSites = scout.room.find(FIND_HOSTILE_CONSTRUCTION_SITES);
        if (enemyConstructionSites.length > 0) {
            scout.goTo(enemyConstructionSites[0].pos);
        }
        // Check if room might be connected to newbie/respawn zone
        let indestructibleWalls = _.filter(scout.room.walls, wall => wall.hits == undefined);
        if (indestructibleWalls.length > 0) { // go back to origin colony if you find a room near newbie zone
            scout.task = Tasks.goToRoom(scout.colony.room.name); // todo: make this more precise
        }
        else {
            // Pick a new room
            let neighboringRooms = _.values(Game.map.describeExits(scout.pos.roomName));
            let roomName = _.sample(neighboringRooms);
            if (Game.map.isRoomAvailable(roomName)) {
                scout.task = Tasks.goToRoom(roomName);
            }
        }
    }
    run() {
        this.autoRun(this.scouts, scout => this.handleScout(scout));
    }
};
RandomWalkerScoutOverlord = __decorate([
    profile
], RandomWalkerScoutOverlord);

// This overlord contains the default actions for any creeps which lack an overlord (for example, miners whose
// miningSite is no longer visible, or guards with no directive)
let DefaultOverlord = class DefaultOverlord extends Overlord {
    constructor(colony) {
        super(colony, 'default', OverlordPriority.default);
        this.idleZerg = [];
    }
    init() {
        // Zergs are collected at end of init phase; by now anything needing to be claimed already has been
        let idleCreeps = _.filter(this.colony.creeps, creep => !getOverlord(creep));
        this.idleZerg = _.map(idleCreeps, creep => Overmind.zerg[creep.name] || new Zerg(creep));
        for (let zerg of this.idleZerg) {
            zerg.refresh();
        }
    }
    run() {
    }
};
DefaultOverlord = __decorate([
    profile
], DefaultOverlord);

// Records one-time and persistent notifications from various in-game events
var NotifierPriority;
(function (NotifierPriority) {
    NotifierPriority[NotifierPriority["Critical"] = 0] = "Critical";
    NotifierPriority[NotifierPriority["High"] = 1] = "High";
    NotifierPriority[NotifierPriority["Normal"] = 2] = "Normal";
    NotifierPriority[NotifierPriority["Low"] = 3] = "Low";
})(NotifierPriority || (NotifierPriority = {}));
class Notifier {
    constructor() {
        this.alerts = [];
        this.notifications = [];
    }
    clear() {
        this.alerts = [];
    }
    alert(message, roomName, priority = NotifierPriority.Normal) {
        // Register an alert to be displayed this in the notifications visual box
        const alert = { message, roomName, priority };
        this.alerts.push(alert);
    }
    // TODO: finish
    notify(message, roomName, duration = 100, email = false) {
        log.alert(printRoomName(roomName) + ': ' + message);
    }
    // init() {
    //
    // }
    //
    // run() {
    //
    // }
    generateNotificationsList(links = false) {
        let sortedAlerts = _.sortBy(this.alerts, alert => alert.priority);
        return _.map(sortedAlerts, alert => {
            if (alert.roomName) {
                return (links ? printRoomName(alert.roomName) : alert.roomName) + ': ' + alert.message;
            }
            else {
                return alert.message;
            }
        });
    }
    visuals() {
        let notificationMessages = this.generateNotificationsList();
        Visualizer.drawNotifications(notificationMessages);
    }
}

const DEFAULT_MAX_PATH_LENGTH = 600;
const DEFAULT_MAX_LINEAR_RANGE = 10;
let Directive = class Directive {
    constructor(flag, requiredRCL = 1) {
        this.memory = flag.memory;
        if (this.memory.suspendUntil) {
            if (Game.time < this.memory.suspendUntil) {
                return;
            }
            else {
                delete this.memory.suspendUntil;
            }
        }
        this.name = flag.name;
        this.ref = flag.ref;
        this.requiredRCL = requiredRCL;
        if (!this.memory.created)
            this.memory.created = Game.time;
        // Relocate flag if needed; this must be called before the colony calculations
        const needsRelocating = this.handleRelocation();
        if (!needsRelocating) {
            this.pos = flag.pos;
            this.room = flag.room;
        }
        const colony = this.getColony();
        // Delete the directive if the colony is dead
        if (!colony) {
            if (Overmind.exceptions.length == 0) {
                log.alert(`Could not get colony for directive ${this.print}; removing flag!`);
                flag.remove();
            }
            else {
                log.alert(`Could not get colony for directive ${this.print}; ` +
                    `exceptions present this tick, so won't remove`);
            }
            return;
        }
        this.colony = colony;
        this.colony.flags.push(flag);
        this.overlords = {};
        // Register directive on Overmind
        Overmind.directives[this.name] = this;
        global[this.name] = this;
        Overmind.overseer.registerDirective(this);
    }
    // Flag must be a getter to avoid caching issues
    get flag() {
        return Game.flags[this.name];
    }
    // get isSuspended(): boolean {
    // 	return !!this.memory.suspendUntil && Game.time < this.memory.suspendUntil;
    // }
    //
    // suspend(ticks: number) {
    // 	this.memory.suspendUntil = Game.time + ticks;
    // }
    //
    // suspendUntil(tick: number) {
    // 	this.memory.suspendUntil = tick;
    // }
    refresh() {
        const flag = this.flag;
        if (!flag) {
            log.warning(`Missing flag for directive ${this.print}! Removing directive.`);
            this.remove();
            return;
        }
        this.memory = flag.memory;
        this.pos = flag.pos;
        this.room = flag.room;
    }
    alert(message, priority = NotifierPriority.Normal) {
        Overmind.overseer.notifier.alert(message, this.pos.roomName, priority);
    }
    get print() {
        return '<a href="#!/room/' + Game.shard.name + '/' + this.pos.roomName + '">[' + this.name + ']</a>';
    }
    handleRelocation() {
        if (this.memory.setPosition) {
            let pos = derefRoomPosition(this.memory.setPosition);
            if (!this.flag.pos.isEqualTo(pos)) {
                let result = this.flag.setPosition(pos);
                if (result == OK) {
                    log.debug(`Moving ${this.name} from ${this.flag.pos.print} to ${pos.print}.`);
                }
                else {
                    log.warning(`Could not set room position to ${JSON.stringify(this.memory.setPosition)}!`);
                }
            }
            else {
                delete this.memory.setPosition;
            }
            this.pos = pos;
            this.room = Game.rooms[pos.roomName];
            return true;
        }
        return false;
    }
    getColony() {
        // If something is written to flag.colony, use that as the colony
        if (this.memory.colony) {
            return Overmind.colonies[this.memory.colony];
        }
        else {
            // If flag contains a colony name as a substring, assign to that colony, regardless of RCL
            let colonyNames = _.keys(Overmind.colonies);
            for (let name of colonyNames) {
                if (this.name.includes(name)) {
                    if (this.name.split(name)[1] != '')
                        continue; // in case of other substring, e.g. E11S12 and E11S1
                    this.memory.colony = name;
                    return Overmind.colonies[name];
                }
            }
            // If flag is in a room belonging to a colony and the colony has sufficient RCL, assign to there
            let colony = Overmind.colonies[Overmind.colonyMap[this.pos.roomName]];
            if (colony && colony.level >= this.requiredRCL) {
                this.memory.colony = colony.name;
                return colony;
            }
            else {
                // Otherwise assign to closest colony
                let nearestColony = this.findNearestColony();
                if (nearestColony) {
                    log.info(`Colony ${nearestColony.room.print} assigned to ${this.name}.`);
                    this.memory.colony = nearestColony.room.name;
                    return nearestColony;
                }
                else {
                    log.error(`Could not find colony match for ${this.name} in ${this.pos.roomName}!` +
                        `Try setting memory.maxPathLength and memory.maxLinearRange.`);
                }
            }
        }
    }
    findNearestColony(verbose = false) {
        const maxPathLength = this.memory.maxPathLength || DEFAULT_MAX_PATH_LENGTH;
        const maxLinearRange = this.memory.maxLinearRange || DEFAULT_MAX_LINEAR_RANGE;
        if (verbose)
            log.info(`Recalculating colony association for ${this.name} in ${this.pos.roomName}`);
        let nearestColony = undefined;
        let minDistance = Infinity;
        let colonyRooms = _.filter(Game.rooms, room => room.my);
        for (let colony of getAllColonies()) {
            if (Game.map.getRoomLinearDistance(this.pos.roomName, colony.name) > maxLinearRange) {
                continue;
            }
            if (colony.level >= this.requiredRCL) {
                let ret = Pathing.findPath((colony.hatchery || colony).pos, this.pos);
                if (!ret.incomplete) {
                    if (ret.path.length < maxPathLength && ret.path.length < minDistance) {
                        nearestColony = colony;
                        minDistance = ret.path.length;
                    }
                    if (verbose)
                        log.info(`Path length to ${colony.room.print}: ${ret.path.length}`);
                }
                else {
                    if (verbose)
                        log.info(`Incomplete path from ${colony.room.print}`);
                }
            }
            else {
                if (verbose) {
                    log.info(`RCL for ${colony.room.print} insufficient: ` +
                        `needs ${this.requiredRCL}, is ${colony.level}`);
                }
            }
        }
        if (nearestColony) {
            return nearestColony;
        }
    }
    // Wrapped flag methods ============================================================================================
    remove(force = false) {
        if (!this.memory.persistent || force) {
            delete Overmind.directives[this.name];
            delete global[this];
            Overmind.overseer.removeDirective(this);
            if (this.colony) {
                _.remove(this.colony.flags, flag => flag.name == this.name);
            }
            if (this.flag) { // check in case flag was removed manually in last build cycle
                return this.flag.remove();
            }
        }
    }
    setColor(color$$1, secondaryColor) {
        if (secondaryColor) {
            return this.flag.setColor(color$$1, secondaryColor);
        }
        else {
            return this.flag.setColor(color$$1);
        }
    }
    setPosition(pos) {
        // Ignore the (x,y) setPosition option since I never use it
        return this.flag.setPosition(pos);
    }
    // Custom directive methods ========================================================================================
    /* Create an appropriate flag to instantiate this directive in the next tick */
    static create(pos, opts = {}) {
        let flagName = opts.name || undefined;
        if (!flagName) {
            flagName = this.directiveName + ':' + randomHex(6);
            if (Game.flags[flagName]) {
                return ERR_NAME_EXISTS;
            }
        }
        if (!opts.quiet) {
            log.alert(`Creating ${this.directiveName} directive at ${pos.print}!`);
        }
        let result = pos.createFlag(flagName, this.color, this.secondaryColor);
        if (result == flagName && opts.memory) {
            Memory.flags[flagName] = opts.memory;
        }
        log.debug(`Result: ${result}, memory: ${JSON.stringify(Memory.flags[result])}`);
        return result;
    }
    /* Whether a directive of the same type is already present (in room | at position) */
    static isPresent(pos, scope) {
        const room = Game.rooms[pos.roomName];
        switch (scope) {
            case 'room':
                if (room) {
                    return _.filter(room.flags, flag => this.filter(flag) &&
                        !(flag.memory.setPosition
                            && flag.memory.setPosition.roomName != pos.roomName)).length > 0;
                }
                else {
                    let flagsInRoom = _.filter(Game.flags, function (flag) {
                        if (flag.memory.setPosition) { // does it need to be relocated?
                            return flag.memory.setPosition.roomName == pos.roomName;
                        }
                        else { // properly located
                            return flag.pos.roomName == pos.roomName;
                        }
                    });
                    return _.filter(flagsInRoom, flag => this.filter(flag)).length > 0;
                }
            case 'pos':
                if (room) {
                    return _.filter(pos.lookFor(LOOK_FLAGS), flag => this.filter(flag) &&
                        !(flag.memory.setPosition
                            && !equalXYR(pos, flag.memory.setPosition))).length > 0;
                }
                else {
                    let flagsAtPos = _.filter(Game.flags, function (flag) {
                        if (flag.memory.setPosition) { // does it need to be relocated?
                            return equalXYR(flag.memory.setPosition, pos);
                        }
                        else { // properly located
                            return equalXYR(flag.pos, pos);
                        }
                    });
                    return _.filter(flagsAtPos, flag => this.filter(flag)).length > 0;
                }
        }
    }
    /* Create a directive if one of the same type is not already present (in room | at position).
     * Calling this method on positions in invisible rooms can be expensive and should be used sparingly. */
    static createIfNotPresent(pos, scope, opts = {}) {
        if (this.isPresent(pos, scope)) {
            return; // do nothing if flag is already here
        }
        let room = Game.rooms[pos.roomName];
        if (!room) {
            if (!opts.memory) {
                opts.memory = {};
            }
            opts.memory.setPosition = pos;
        }
        let flagsOfThisType;
        switch (scope) {
            case 'room':
                if (room) {
                    return this.create(pos, opts);
                }
                else {
                    log.info(`Creating directive at ${pos.print}... ` +
                        `No visibility in room; directive will be relocated on next tick.`);
                    let createAtPos;
                    if (opts.memory && opts.memory.colony) {
                        createAtPos = Pathing.findPathablePosition(opts.memory.colony);
                    }
                    else {
                        createAtPos = Pathing.findPathablePosition(_.first(getAllColonies()).room.name);
                    }
                    return this.create(createAtPos, opts);
                }
            case 'pos':
                if (room) {
                    return this.create(pos, opts);
                }
                else {
                    log.info(`Creating directive at ${pos.print}... ` +
                        `No visibility in room; directive will be relocated on next tick.`);
                    let createAtPos;
                    if (opts.memory && opts.memory.colony) {
                        createAtPos = Pathing.findPathablePosition(opts.memory.colony);
                    }
                    else {
                        createAtPos = Pathing.findPathablePosition(_.first(getAllColonies()).room.name);
                    }
                    return this.create(createAtPos, opts);
                }
        }
    }
    /* Filter for _.filter() that checks if a flag is of the matching type */
    static filter(flag) {
        return flag.color == this.color && flag.secondaryColor == this.secondaryColor;
    }
    /* Map a list of flags to directives, accepting a filter */
    static find(flags) {
        flags = _.filter(flags, flag => this.filter(flag));
        return _.compact(_.map(flags, flag => Overmind.directives[flag.name]));
    }
    // Overwrite this in child classes to display relevant information
    visuals() {
    }
};
Directive = __decorate([
    profile
], Directive);

let ReservingOverlord = class ReservingOverlord extends Overlord {
    constructor(directive, priority = OverlordPriority.remoteRoom.reserve) {
        super(directive, 'reserve', priority);
        // Change priority to operate per-outpost
        this.priority += this.outpostIndex * OverlordPriority.remoteRoom.roomIncrement;
        this.reserveBuffer = 2000;
        this.reservers = this.zerg(Roles.claim);
    }
    init() {
        let amount = 0;
        if (this.room) {
            if (this.room.controller.needsReserving(this.reserveBuffer)) {
                amount = 1;
            }
        }
        else if (RoomIntel.roomReservedBy(this.pos.roomName) == MY_USERNAME &&
            RoomIntel.roomReservationRemaining(this.pos.roomName) < 1000) {
            amount = 1;
        }
        this.wishlist(amount, Setups.infestors.reserve);
    }
    handleReserver(reserver) {
        if (reserver.room == this.room && !reserver.pos.isEdge) {
            // If reserver is in the room and not on exit tile
            if (!this.room.controller.signedByMe) {
                // Takes care of an edge case where planned newbie zone signs prevents signing until room is reserved
                if (!this.room.my && this.room.controller.signedByScreeps) {
                    reserver.task = Tasks.reserve(this.room.controller);
                }
                else {
                    reserver.task = Tasks.signController(this.room.controller);
                }
            }
            else {
                reserver.task = Tasks.reserve(this.room.controller);
            }
        }
        else {
            // reserver.task = Tasks.goTo(this.pos);
            reserver.goTo(this.pos);
        }
    }
    run() {
        this.autoRun(this.reservers, reserver => this.handleReserver(reserver));
    }
};
ReservingOverlord = __decorate([
    profile
], ReservingOverlord);

let StationaryScoutOverlord = class StationaryScoutOverlord extends Overlord {
    constructor(directive, priority = OverlordPriority.scouting.stationary) {
        super(directive, 'scout', priority);
        this.scouts = this.zerg(Roles.scout, { notifyWhenAttacked: false });
    }
    init() {
        this.wishlist(1, Setups.scout);
    }
    run() {
        for (let scout of this.scouts) {
            if (!(scout.pos.inRangeTo(this.pos, 3) && !scout.pos.isEdge)) {
                scout.goTo(this.pos, { range: 3 });
            }
        }
    }
};
StationaryScoutOverlord = __decorate([
    profile
], StationaryScoutOverlord);

var DirectiveOutpost_1;
let DirectiveOutpost = DirectiveOutpost_1 = class DirectiveOutpost extends Directive {
    constructor(flag) {
        super(flag);
        // if (!this.room) {
        // 	// Push source / output positions to colony.destinations if room is invisible for correct road routings
        // 	let savedSources = Memory.rooms[this.pos.roomName] ? Memory.rooms[this.pos.roomName].src || [] : [];
        // 	for (let src of savedSources) {
        // 		let pos: RoomPosition;
        // 		if (src.contnr) {
        // 			pos = derefCoords(src.contnr, this.pos.roomName);
        // 		} else {
        // 			pos = derefCoords(src.c, this.pos.roomName);
        // 		}
        // 		this.colony.destinations.push(pos);
        // 	}
        // }
    }
    spawnMoarOverlords() {
        if (this.colony.level >= DirectiveOutpost_1.settings.canSpawnReserversAtRCL) {
            if (Cartographer.roomType(this.pos.roomName) == ROOMTYPE_CONTROLLER) {
                this.overlords.reserve = new ReservingOverlord(this);
            }
        }
        else {
            this.overlords.scout = new StationaryScoutOverlord(this);
        }
    }
    init() {
    }
    run() {
        if (RoomIntel.roomOwnedBy(this.pos.roomName)) {
            log.warning(`Removing ${this.print} since room is owned!`);
            this.remove();
        }
        if (Game.time % 10 == 3 && this.room && this.room.controller
            && !this.pos.isEqualTo(this.room.controller.pos) && !this.memory.setPosition) {
            this.setPosition(this.room.controller.pos);
        }
    }
};
DirectiveOutpost.directiveName = 'outpost';
DirectiveOutpost.color = COLOR_PURPLE;
DirectiveOutpost.secondaryColor = COLOR_PURPLE;
DirectiveOutpost.settings = {
    canSpawnReserversAtRCL: 3,
};
DirectiveOutpost = DirectiveOutpost_1 = __decorate([
    profile
], DirectiveOutpost);

var MiningOverlord_1;
const StandardMinerSetupCost = bodyCost(Setups.drones.miners.standard.generateBody(Infinity));
const DoubleMinerSetupCost = bodyCost(Setups.drones.miners.double.generateBody(Infinity));
const BUILD_OUTPUT_FREQUENCY = 15;
let MiningOverlord = MiningOverlord_1 = class MiningOverlord extends Overlord {
    constructor(directive, priority) {
        super(directive, 'mine', priority);
        this.directive = directive;
        this.priority += this.outpostIndex * OverlordPriority.remoteRoom.roomIncrement;
        this.miners = this.zerg(Roles.drone);
        // Populate structures
        this.populateStructures();
        // Compute energy output
        if (Cartographer.roomType(this.pos.roomName) == ROOMTYPE_SOURCEKEEPER) {
            this.energyPerTick = SOURCE_ENERGY_KEEPER_CAPACITY / ENERGY_REGEN_TIME;
        }
        else if (this.colony.level >= DirectiveOutpost.settings.canSpawnReserversAtRCL) {
            this.energyPerTick = SOURCE_ENERGY_CAPACITY / ENERGY_REGEN_TIME;
        }
        else {
            this.energyPerTick = SOURCE_ENERGY_NEUTRAL_CAPACITY / ENERGY_REGEN_TIME;
        }
        this.miningPowerNeeded = Math.ceil(this.energyPerTick / HARVEST_POWER) + 1;
        // Decide operating mode
        if (Cartographer.roomType(this.pos.roomName) == ROOMTYPE_SOURCEKEEPER) {
            this.mode = 'SK';
            this.setup = Setups.drones.miners.sourceKeeper;
        }
        else if (this.colony.room.energyCapacityAvailable < StandardMinerSetupCost) {
            this.mode = 'early';
            this.setup = Setups.drones.miners.default;
        }
        else if (this.link) {
            this.mode = 'link';
            this.setup = Setups.drones.miners.default;
        }
        else {
            this.mode = 'standard';
            this.setup = Setups.drones.miners.standard;
            // todo: double miner condition
        }
        const miningPowerEach = this.setup.getBodyPotential(WORK, this.colony);
        this.minersNeeded = Math.min(Math.ceil(this.miningPowerNeeded / miningPowerEach), this.pos.availableNeighbors(true).length);
        // Allow drop mining at low levels
        this.allowDropMining = this.colony.level < MiningOverlord_1.settings.dropMineUntilRCL;
        if (this.mode != 'early' && !this.allowDropMining) {
            if (this.container) {
                this.harvestPos = this.container.pos;
            }
            else if (this.link) {
                this.harvestPos = _.find(this.link.pos.availableNeighbors(true), pos => pos.getRangeTo(this) == 1);
            }
            else {
                this.harvestPos = this.calculateContainerPos();
            }
        }
    }
    get distance() {
        return this.directive.distance;
    }
    populateStructures() {
        if (Game.rooms[this.pos.roomName]) {
            this.source = _.first(this.pos.lookFor(LOOK_SOURCES));
            this.constructionSite = _.first(this.pos.findInRange(FIND_MY_CONSTRUCTION_SITES, 2));
            this.container = this.pos.findClosestByLimitedRange(Game.rooms[this.pos.roomName].containers, 1);
            this.link = this.pos.findClosestByLimitedRange(this.colony.availableLinks, 2);
            // if (this.link) { // this won't cause repopulation problems since link rooms are always visible
            // 	this.colony.linkNetwork.claimLink(this.link);
            // }
        }
    }
    refresh() {
        if (!this.room && Game.rooms[this.pos.roomName]) { // if you just gained vision of this room
            this.populateStructures();
        }
        // if (!this.allowDropMining && Game.time % 100 == 0 && !this.container && !this.link) {
        // 	log.warning(`Mining site at ${this.pos.print} has no output!`);
        // }
        super.refresh();
        $.refresh(this, 'source', 'container', 'link', 'constructionSite');
    }
    /* Calculate where the container output will be built for this site */
    calculateContainerPos() {
        // log.debug(`Computing container position for mining overlord at ${this.pos.print}...`);
        let originPos = undefined;
        if (this.colony.storage) {
            originPos = this.colony.storage.pos;
        }
        else if (this.colony.roomPlanner.storagePos) {
            originPos = this.colony.roomPlanner.storagePos;
        }
        if (originPos) {
            let path = Pathing.findShortestPath(this.pos, originPos).path;
            let pos = _.find(path, pos => pos.getRangeTo(this) == 1);
            if (pos)
                return pos;
        }
        // Shouldn't ever get here
        log.warning(`Last resort container position calculation for ${this.print}!`);
        return _.first(this.pos.availableNeighbors(true));
    }
    /* Add or remove containers as needed to keep exactly one of contaner | link */
    addRemoveContainer() {
        if (this.allowDropMining) {
            return; // only build containers in reserved, owned, or SK rooms
        }
        // Create container if there is not already one being built and no link
        if (!this.container && !this.constructionSite && !this.link) {
            let containerPos = this.calculateContainerPos();
            log.info(`${this.print}: building container at ${containerPos.print}`);
            let result = containerPos.createConstructionSite(STRUCTURE_CONTAINER);
            if (result != OK) {
                log.error(`${this.print}: cannot build container at ${containerPos.print}! Result: ${result}`);
            }
            return;
        }
        // Destroy container if link is nearby
        if (this.container && this.link) {
            // safety checks
            if (this.colony.hatchery && this.container.pos.getRangeTo(this.colony.hatchery) > 2 &&
                this.container.pos.getRangeTo(this.colony.upgradeSite) > 3) {
                log.info(`${this.print}: container and link present; destroying container at ${this.container.pos.print}`);
                this.container.destroy();
            }
        }
    }
    registerEnergyRequests() {
        if (this.container) {
            let transportCapacity = 200 * this.colony.level;
            let threshold = this.colony.stage > ColonyStage.Larva ? 0.8 : 0.5;
            if (_.sum(this.container.store) > threshold * transportCapacity) {
                this.colony.logisticsNetwork.requestOutput(this.container, {
                    resourceType: 'all',
                    dAmountdt: this.energyPerTick
                });
            }
        }
        if (this.link) {
            // If the link will be full with next deposit from the miner
            let minerCapacity = 150;
            if (this.link.energy + minerCapacity > this.link.energyCapacity) {
                this.colony.linkNetwork.requestTransmit(this.link);
            }
        }
    }
    init() {
        this.wishlist(this.minersNeeded, this.setup);
        this.registerEnergyRequests();
    }
    earlyMiningActions(miner) {
        if (miner.room != this.room) {
            return miner.goToRoom(this.pos.roomName);
        }
        // Container mining
        if (this.container) {
            if (this.container.hits < this.container.hitsMax
                && miner.carry.energy >= REPAIR_POWER * miner.getActiveBodyparts(WORK)) {
                return miner.goRepair(this.container);
            }
            else {
                if (_.sum(miner.carry) < miner.carryCapacity) {
                    return miner.goHarvest(this.source);
                }
                else {
                    return miner.goTransfer(this.container);
                }
            }
        }
        // Build output site
        if (this.constructionSite) {
            if (miner.carry.energy >= BUILD_POWER * miner.getActiveBodyparts(WORK)) {
                return miner.goBuild(this.constructionSite);
            }
            else {
                return miner.goHarvest(this.source);
            }
        }
        // Drop mining
        if (this.allowDropMining) {
            miner.goHarvest(this.source);
            if (miner.carry.energy > 0.8 * miner.carryCapacity) { // try to drop on top of largest drop if full
                let biggestDrop = maxBy(miner.pos.findInRange(miner.room.droppedEnergy, 1), drop => drop.amount);
                if (biggestDrop) {
                    miner.goDrop(biggestDrop.pos, RESOURCE_ENERGY);
                }
            }
            return;
        }
    }
    linkMiningActions(miner) {
        // Approach mining site
        if (this.goToMiningSite(miner))
            return;
        // Link mining
        if (this.link) {
            miner.harvest(this.source);
            if (miner.carry.energy > 0.9 * miner.carryCapacity) {
                miner.transfer(this.link, RESOURCE_ENERGY);
            }
            return;
        }
        else {
            log.warning(`Link miner ${miner.print} has no link!`);
        }
    }
    standardMiningActions(miner) {
        // Approach mining site
        if (this.goToMiningSite(miner))
            return;
        // Container mining
        if (this.container) {
            if (this.container.hits < this.container.hitsMax
                && miner.carry.energy >= REPAIR_POWER * miner.getActiveBodyparts(WORK)) {
                return miner.repair(this.container);
            }
            else {
                return miner.harvest(this.source);
            }
        }
        // Build output site
        if (this.constructionSite) {
            if (miner.carry.energy >= BUILD_POWER * miner.getActiveBodyparts(WORK)) {
                return miner.build(this.constructionSite);
            }
            else {
                return miner.harvest(this.source);
            }
        }
        // Drop mining
        if (this.allowDropMining) {
            miner.harvest(this.source);
            if (miner.carry.energy > 0.8 * miner.carryCapacity) { // move over the drop when you're close to full
                let biggestDrop = maxBy(miner.pos.findInRange(miner.room.droppedEnergy, 1), drop => drop.amount);
                if (biggestDrop) {
                    miner.goTo(biggestDrop);
                }
            }
            if (miner.carry.energy == miner.carryCapacity) { // drop when you are full
                miner.drop(RESOURCE_ENERGY);
            }
            return;
        }
    }
    goToMiningSite(miner) {
        // Move onto harvesting position or near to source (depending on early/standard mode)
        if (this.harvestPos) {
            if (!miner.pos.inRangeToPos(this.harvestPos, 0)) {
                miner.goTo(this.harvestPos);
                return true;
            }
        }
        else {
            if (!miner.pos.inRangeToPos(this.pos, 1)) {
                miner.goTo(this);
                return true;
            }
        }
        return false;
    }
    handleMiner(miner) {
        // Flee hostiles
        if (miner.flee(miner.room.fleeDefaults, { dropEnergy: true })) {
            return;
        }
        // Move onto harvesting position or near to source (depending on early/standard mode)
        if (this.mode == 'early' || !this.harvestPos) {
            if (!miner.pos.inRangeToPos(this.pos, 1)) {
                return miner.goTo(this);
            }
        }
        else {
            if (!miner.pos.inRangeToPos(this.harvestPos, 0)) {
                return miner.goTo(this.harvestPos, { range: 0 });
            }
        }
        switch (this.mode) {
            case 'early':
                return this.earlyMiningActions(miner);
            case 'link':
                return this.linkMiningActions(miner);
            case 'standard':
                return this.standardMiningActions(miner);
            case 'SK':
                return this.standardMiningActions(miner);
            case 'double':
                return this.standardMiningActions(miner);
            default:
                log.error(`UNHANDLED MINER STATE FOR ${miner.print} (MODE: ${this.mode})`);
        }
    }
    run() {
        for (let miner of this.miners) {
            this.handleMiner(miner);
        }
        if (this.room && Game.time % BUILD_OUTPUT_FREQUENCY == 1) {
            this.addRemoveContainer();
        }
    }
};
MiningOverlord.settings = {
    minLinkDistance: 10,
    dropMineUntilRCL: 3,
};
MiningOverlord = MiningOverlord_1 = __decorate([
    profile
], MiningOverlord);

const defaultDirectiveHarvestMemory = {
    stats: {
        usage: 1,
        downtime: 0,
    }
};
let DirectiveHarvest = class DirectiveHarvest extends Directive {
    constructor(flag) {
        super(flag);
        if (this.colony) {
            this.colony.miningSites[this.name] = this;
            this.colony.destinations.push({ pos: this.pos, order: this.memory.created || Game.time });
        }
        _.defaultsDeep(this.memory, defaultDirectiveHarvestMemory);
    }
    // Hauling distance
    get distance() {
        if (!this.memory.pathing || Game.time >= this.memory.pathing.expiration) {
            let distance = Pathing.distance(this.colony.pos, this.pos);
            let expiration = getCacheExpiration(this.colony.storage ? 5000 : 1000);
            this.memory.pathing = { distance, expiration };
        }
        return this.memory.pathing.distance;
    }
    spawnMoarOverlords() {
        // Create a mining overlord for this
        let priority = OverlordPriority.ownedRoom.mine;
        if (!(this.room && this.room.my)) {
            priority = Cartographer.roomType(this.pos.roomName) == ROOMTYPE_SOURCEKEEPER ?
                OverlordPriority.remoteSKRoom.mine : OverlordPriority.remoteRoom.mine;
        }
        this.overlords.mine = new MiningOverlord(this, priority);
    }
    init() {
    }
    run() {
        this.computeStats();
    }
    computeStats() {
        const source = this.overlords.mine.source;
        if (source && source.ticksToRegeneration == 1) {
            this.memory.stats.usage = (source.energyCapacity - source.energy) / source.energyCapacity;
        }
        const container = this.overlords.mine.container;
        this.memory.stats.downtime = exponentialMovingAverage(container ? +container.isFull : 0, this.memory.stats.downtime, CREEP_LIFE_TIME);
    }
};
DirectiveHarvest.directiveName = 'harvest';
DirectiveHarvest.color = COLOR_YELLOW;
DirectiveHarvest.secondaryColor = COLOR_YELLOW;
DirectiveHarvest = __decorate([
    profile
], DirectiveHarvest);

var ExtractorOverlord_1;
const BUILD_OUTPUT_FREQUENCY$1 = 15;
let ExtractorOverlord = ExtractorOverlord_1 = class ExtractorOverlord extends Overlord {
    constructor(directive, priority) {
        super(directive, 'mineral', priority);
        this.directive = directive;
        this.priority += this.outpostIndex * OverlordPriority.remoteSKRoom.roomIncrement;
        this.drones = this.zerg(Roles.drone);
        // Populate structures
        this.populateStructures();
    }
    populateStructures() {
        if (Game.rooms[this.pos.roomName]) {
            this.extractor = this.pos.lookForStructure(STRUCTURE_EXTRACTOR);
            this.mineral = this.pos.lookFor(LOOK_MINERALS)[0];
            this.container = this.pos.findClosestByLimitedRange(Game.rooms[this.pos.roomName].containers, 1);
        }
    }
    refresh() {
        if (!this.room && Game.rooms[this.pos.roomName]) { // if you just gained vision of this room
            this.populateStructures();
        }
        super.refresh();
        $.refresh(this, 'extractor', 'mineral', 'container');
    }
    registerOutputRequests() {
        if (this.container) {
            if (_.sum(this.container.store) > 0.5 * this.container.storeCapacity ||
                (_.sum(this.container.store) > 0 && this.drones.length == 0)) {
                this.colony.logisticsNetwork.requestOutput(this.container, { resourceType: 'all' });
            }
        }
    }
    /* Calculate where the container output will be built for this site */
    calculateContainerPos() {
        // log.debug(`Computing container position for mining overlord at ${this.pos.print}...`);
        let originPos = undefined;
        if (this.colony.storage) {
            originPos = this.colony.storage.pos;
        }
        else if (this.colony.roomPlanner.storagePos) {
            originPos = this.colony.roomPlanner.storagePos;
        }
        if (originPos) {
            let path = Pathing.findShortestPath(this.pos, originPos).path;
            let pos = _.find(path, pos => pos.getRangeTo(this) == 1);
            if (pos)
                return pos;
        }
        // Shouldn't ever get here
        log.warning(`Last resort container position calculation for ${this.print}!`);
        return _.first(this.pos.availableNeighbors(true));
    }
    buildOutputIfNeeded() {
        // Create container if there is not already one being built and no link
        if (!this.container) {
            let containerSite = _.first(_.filter(this.pos.findInRange(FIND_MY_CONSTRUCTION_SITES, 2), site => site.structureType == STRUCTURE_CONTAINER));
            if (!containerSite) {
                let containerPos = this.calculateContainerPos();
                log.info(`${this.print}: building container at ${containerPos.print}`);
                let result = containerPos.createConstructionSite(STRUCTURE_CONTAINER);
                if (result != OK) {
                    log.error(`${this.print}: cannot build container at ${containerPos.print}! Result: ${result}`);
                }
                return;
            }
        }
    }
    init() {
        let amount = this.mineral && this.mineral.mineralAmount > 0 ? this.mineral.pos.availableNeighbors().length : 0;
        this.wishlist(Math.min(amount, ExtractorOverlord_1.settings.maxDrones), Setups.drones.extractor);
        this.registerOutputRequests();
    }
    handleDrone(drone) {
        // Ensure you are in the assigned room
        if (drone.room == this.room && !drone.pos.isEdge) {
            if (_.sum(drone.carry) == 0) {
                drone.task = Tasks.harvest(this.mineral);
            }
            // Else see if there is an output to depsit to or to maintain
            else if (this.container) {
                drone.task = Tasks.transferAll(this.container);
                // Move onto the output container if you're the only drone
                if (!drone.pos.isEqualTo(this.container.pos) && this.drones.length == 1) {
                    drone.goTo(this.container, { range: 0 });
                }
            }
        }
        else {
            drone.goTo(this);
        }
    }
    run() {
        this.autoRun(this.drones, drone => this.handleDrone(drone), drone => drone.flee());
        if (this.room && Game.time % BUILD_OUTPUT_FREQUENCY$1 == 2) {
            this.buildOutputIfNeeded();
        }
    }
};
ExtractorOverlord.settings = {
    maxDrones: 2,
};
ExtractorOverlord = ExtractorOverlord_1 = __decorate([
    profile
], ExtractorOverlord);

let DirectiveExtract = class DirectiveExtract extends Directive {
    constructor(flag) {
        super(flag);
        if (this.colony) {
            this.colony.destinations.push({ pos: this.pos, order: this.memory.created || Game.time });
        }
    }
    spawnMoarOverlords() {
        let priority;
        if (this.room && this.room.my) {
            if (this.colony.level == 8) {
                priority = OverlordPriority.ownedRoom.mineralRCL8;
            }
            else {
                priority = OverlordPriority.ownedRoom.mineral;
            }
        }
        else {
            priority = OverlordPriority.remoteSKRoom.mineral;
        }
        this.overlords.extract = new ExtractorOverlord(this, priority);
    }
    init() {
    }
    run() {
        if (this.colony.level < 6) {
            log.notify(`Removing extraction directive in ${this.pos.roomName}: room RCL insufficient.`);
            this.remove();
        }
    }
};
DirectiveExtract.directiveName = 'extract';
DirectiveExtract.color = COLOR_YELLOW;
DirectiveExtract.secondaryColor = COLOR_CYAN;
DirectiveExtract = __decorate([
    profile
], DirectiveExtract);

// Colony class - organizes all assets of an owned room into a colony
var ColonyStage;
(function (ColonyStage) {
    ColonyStage[ColonyStage["Larva"] = 0] = "Larva";
    ColonyStage[ColonyStage["Pupa"] = 1] = "Pupa";
    ColonyStage[ColonyStage["Adult"] = 2] = "Adult";
})(ColonyStage || (ColonyStage = {}));
var DEFCON;
(function (DEFCON) {
    DEFCON[DEFCON["safe"] = 0] = "safe";
    DEFCON[DEFCON["invasionNPC"] = 1] = "invasionNPC";
    DEFCON[DEFCON["boostedInvasionNPC"] = 2] = "boostedInvasionNPC";
    DEFCON[DEFCON["playerInvasion"] = 2] = "playerInvasion";
    DEFCON[DEFCON["bigPlayerInvasion"] = 3] = "bigPlayerInvasion";
})(DEFCON || (DEFCON = {}));
function getAllColonies() {
    return _.values(Overmind.colonies);
}
const defaultColonyMemory = {
    defcon: {
        level: DEFCON.safe,
        tick: -Infinity
    },
    expansionData: {
        possibleExpansions: {},
        expiration: 0,
    },
};
let Colony = class Colony {
    constructor(id, roomName, outposts) {
        // Primitive colony setup
        this.id = id;
        this.name = roomName;
        this.ref = roomName;
        this.memory = Mem.wrap(Memory.colonies, roomName, defaultColonyMemory, true);
        // Register colony globally to allow 'W1N1' and 'w1n1' to refer to Overmind.colonies.W1N1
        global[this.name] = this;
        global[this.name.toLowerCase()] = this;
        // Build the colony
        this.build(roomName, outposts);
    }
    get print() {
        return '<a href="#!/room/' + Game.shard.name + '/' + this.room.name + '">[' + this.name + ']</a>';
    }
    build(roomName, outposts) {
        // Register rooms
        this.roomNames = [roomName].concat(outposts);
        this.room = Game.rooms[roomName];
        this.outposts = _.compact(_.map(outposts, outpost => Game.rooms[outpost]));
        this.rooms = [this.room].concat(this.outposts);
        this.miningSites = {}; // filled in by harvest directives
        this.extractionSites = {}; // filled in by extract directives
        // Register creeps
        this.creeps = Overmind.cache.creepsByColony[this.name] || [];
        this.creepsByRole = _.groupBy(this.creeps, creep => creep.memory.role);
        // Register the rest of the colony components; the order in which these are called is important!
        this.registerRoomObjects_cached(); // Register real colony components
        this.registerOperationalState(); // Set the colony operational state
        this.registerUtilities(); // Register logistics utilities, room planners, and layout info
        this.registerHiveClusters(); // Build the hive clusters
        /* Colony.spawnMoarOverlords() gets called from Overmind.ts, along with Directive.spawnMoarOverlords() */
    }
    refresh() {
        this.memory = Mem.wrap(Memory.colonies, this.room.name, defaultColonyMemory, true);
        // Refresh rooms
        this.room = Game.rooms[this.room.name];
        this.outposts = _.compact(_.map(this.outposts, outpost => Game.rooms[outpost.name]));
        this.rooms = [this.room].concat(this.outposts);
        // refresh creeps
        this.creeps = Overmind.cache.creepsByColony[this.name] || [];
        this.creepsByRole = _.groupBy(this.creeps, creep => creep.memory.role);
        // Register the rest of the colony components; the order in which these are called is important!
        this.refreshRoomObjects();
        this.registerOperationalState();
        this.refreshUtilities();
        this.refreshHiveClusters();
    }
    registerRoomObjects() {
        // Create placeholder arrays for remaining properties to be filled in by the Overmind
        this.flags = []; // filled in by directives
        this.destinations = []; // filled in by various hive clusters and directives
        // Register room objects across colony rooms
        this.controller = this.room.controller; // must be controller since colonies are based in owned rooms
        this.spawns = _.sortBy(_.filter(this.room.spawns, spawn => spawn.my && spawn.isActive()), spawn => spawn.ref);
        this.extensions = this.room.extensions;
        this.storage = this.room.storage && this.room.storage.isActive() ? this.room.storage : undefined;
        this.links = this.room.links;
        this.availableLinks = _.clone(this.room.links);
        this.terminal = this.room.terminal && this.room.terminal.isActive() ? this.room.terminal : undefined;
        this.towers = this.room.towers;
        this.labs = _.sortBy(_.filter(this.room.labs, lab => lab.my && lab.isActive()), lab => 50 * lab.pos.y + lab.pos.x); // Labs are sorted in reading order of positions
        this.powerSpawn = this.room.powerSpawn;
        this.nuker = this.room.nuker;
        this.observer = this.room.observer;
        this.pos = (this.storage || this.terminal || this.spawns[0] || this.controller).pos;
        // Register physical objects across all rooms in the colony
        this.sources = _.sortBy(_.flatten(_.map(this.rooms, room => room.sources)), source => source.pos.getMultiRoomRangeTo(this.pos));
        this.extractors = _(this.rooms)
            .map(room => room.extractor)
            .compact()
            .filter(extractor => (extractor.my && extractor.room.my)
            || Cartographer.roomType(extractor.room.name) != ROOMTYPE_CONTROLLER)
            .sortBy(extractor => extractor.pos.getMultiRoomRangeTo(this.pos)).value();
        this.constructionSites = _.flatten(_.map(this.rooms, room => room.constructionSites));
        this.tombstones = _.flatten(_.map(this.rooms, room => room.tombstones));
        this.drops = _.merge(_.map(this.rooms, room => room.drops));
        this.repairables = _.flatten(_.map(this.rooms, room => room.repairables));
        this.rechargeables = _.flatten(_.map(this.rooms, room => room.rechargeables));
        // Register assets
        this.assets = this.getAllAssets();
    }
    registerRoomObjects_cached() {
        // Create placeholder arrays for remaining properties to be filled in by the Overmind
        this.flags = []; // filled in by directives
        this.destinations = []; // filled in by various hive clusters and directives
        // Register room objects across colony rooms
        this.controller = this.room.controller; // must be controller since colonies are based in owned rooms
        this.extensions = this.room.extensions;
        this.links = this.room.links;
        this.availableLinks = _.clone(this.room.links);
        this.towers = this.room.towers;
        this.powerSpawn = this.room.powerSpawn;
        this.nuker = this.room.nuker;
        this.observer = this.room.observer;
        $.set(this, 'spawns', () => _.sortBy(_.filter(this.room.spawns, spawn => spawn.my && spawn.isActive()), spawn => spawn.ref));
        $.set(this, 'storage', () => this.room.storage && this.room.storage.isActive() ? this.room.storage : undefined);
        // this.availableLinks = _.clone(this.room.links);
        $.set(this, 'terminal', () => this.room.terminal && this.room.terminal.isActive() ? this.room.terminal : undefined);
        $.set(this, 'labs', () => _.sortBy(_.filter(this.room.labs, lab => lab.my && lab.isActive()), lab => 50 * lab.pos.y + lab.pos.x));
        this.pos = (this.storage || this.terminal || this.spawns[0] || this.controller).pos;
        // Register physical objects across all rooms in the colony
        $.set(this, 'sources', () => _.sortBy(_.flatten(_.map(this.rooms, room => room.sources)), source => source.pos.getMultiRoomRangeTo(this.pos)));
        for (let source of this.sources) {
            DirectiveHarvest.createIfNotPresent(source.pos, 'pos');
        }
        $.set(this, 'extractors', () => _(this.rooms)
            .map(room => room.extractor)
            .compact()
            .filter(e => (e.my && e.room.my)
            || Cartographer.roomType(e.room.name) != ROOMTYPE_CONTROLLER)
            .sortBy(e => e.pos.getMultiRoomRangeTo(this.pos)).value());
        if (this.controller.level >= 6) {
            _.forEach(this.extractors, extractor => DirectiveExtract.createIfNotPresent(extractor.pos, 'pos'));
        }
        $.set(this, 'repairables', () => _.flatten(_.map(this.rooms, room => room.repairables)));
        $.set(this, 'rechargeables', () => _.flatten(_.map(this.rooms, room => room.rechargeables)));
        $.set(this, 'constructionSites', () => _.flatten(_.map(this.rooms, room => room.constructionSites)), 10);
        $.set(this, 'tombstones', () => _.flatten(_.map(this.rooms, room => room.tombstones)), 5);
        this.drops = _.merge(_.map(this.rooms, room => room.drops));
        // Register assets
        this.assets = this.getAllAssets();
    }
    refreshRoomObjects() {
        $.refresh(this, 'controller', 'extensions', 'links', 'towers', 'powerSpawn', 'nuker', 'observer', 'spawns', 'storage', 'terminal', 'labs', 'sources', 'extractors', 'constructionSites', 'repairables', 'rechargeables');
        $.set(this, 'constructionSites', () => _.flatten(_.map(this.rooms, room => room.constructionSites)), 10);
        $.set(this, 'tombstones', () => _.flatten(_.map(this.rooms, room => room.tombstones)), 5);
        this.drops = _.merge(_.map(this.rooms, room => room.drops));
        // Re-compute assets
        this.assets = this.getAllAssets();
    }
    registerOperationalState() {
        this.level = this.controller.level;
        this.bootstrapping = false;
        this.isIncubating = false;
        if (this.storage && this.spawns[0]) {
            // If the colony has storage and a hatchery
            if (this.controller.level == 8) {
                this.stage = ColonyStage.Adult;
            }
            else {
                this.stage = ColonyStage.Pupa;
            }
        }
        else {
            this.stage = ColonyStage.Larva;
        }
        // this.incubatingColonies = [];
        this.lowPowerMode = Energetics.lowPowerMode(this);
        // Set DEFCON level
        // TODO: finish this
        let defcon = DEFCON.safe;
        let defconDecayTime = 200;
        if (this.room.dangerousHostiles.length > 0 && !this.controller.safeMode) {
            let effectiveHostileCount = _.sum(_.map(this.room.dangerousHostiles, hostile => hostile.boosts.length > 0 ? 2 : 1));
            if (effectiveHostileCount >= 3) {
                defcon = DEFCON.boostedInvasionNPC;
            }
            else {
                defcon = DEFCON.invasionNPC;
            }
        }
        if (this.memory.defcon) {
            if (defcon < this.memory.defcon.level) { // decay defcon level over time if defcon less than memory value
                if (this.memory.defcon.tick + defconDecayTime < Game.time) {
                    this.memory.defcon.level = defcon;
                    this.memory.defcon.tick = Game.time;
                }
            }
            else if (defcon > this.memory.defcon.level) { // refresh defcon time if it increases by a level
                this.memory.defcon.level = defcon;
                this.memory.defcon.tick = Game.time;
            }
        }
        else {
            this.memory.defcon = {
                level: defcon,
                tick: Game.time
            };
        }
        this.defcon = this.memory.defcon.level;
        this.breached = (this.room.dangerousHostiles.length > 0 &&
            this.creeps.length == 0 &&
            !this.controller.safeMode);
        this.terminalState = undefined;
    }
    registerUtilities() {
        // Resource requests
        this.linkNetwork = new LinkNetwork(this);
        this.logisticsNetwork = new LogisticsNetwork(this);
        this.transportRequests = new TransportRequestGroup();
        // Register a room planner
        this.roomPlanner = new RoomPlanner(this);
        if (this.roomPlanner.memory.bunkerData && this.roomPlanner.memory.bunkerData.anchor) {
            this.layout = 'bunker';
            let anchor = derefRoomPosition(this.roomPlanner.memory.bunkerData.anchor);
            // log.debug(JSON.stringify(`anchor for ${this.name}: ${anchor}`));
            let spawnPositions = _.map(bunkerLayout[8].buildings.spawn.pos, c => getPosFromBunkerCoord(c, this));
            // log.debug(JSON.stringify(`spawnPositions for ${this.name}: ${spawnPositions}`));
            let rightSpawnPos = maxBy(spawnPositions, pos => pos.x);
            let topSpawnPos = minBy(spawnPositions, pos => pos.y);
            let coreSpawnPos = anchor.findClosestByRange(spawnPositions);
            // log.debug(JSON.stringify(`spawnPoses: ${rightSpawnPos}, ${topSpawnPos}, ${coreSpawnPos}`));
            this.bunker = {
                anchor: anchor,
                topSpawn: topSpawnPos.lookForStructure(STRUCTURE_SPAWN),
                coreSpawn: coreSpawnPos.lookForStructure(STRUCTURE_SPAWN),
                rightSpawn: rightSpawnPos.lookForStructure(STRUCTURE_SPAWN),
            };
        }
        else {
            this.layout = 'twoPart';
        }
        // Register road network
        this.roadLogistics = new RoadLogistics(this);
        // "Organism Abathur with you."
        this.abathur = new Abathur(this);
    }
    refreshUtilities() {
        this.linkNetwork.refresh();
        this.logisticsNetwork.refresh();
        this.transportRequests.refresh();
        this.roomPlanner.refresh();
        if (this.bunker) {
            if (this.bunker.topSpawn) {
                this.bunker.topSpawn = Game.getObjectById(this.bunker.topSpawn.id);
            }
            if (this.bunker.coreSpawn) {
                this.bunker.coreSpawn = Game.getObjectById(this.bunker.coreSpawn.id);
            }
            if (this.bunker.rightSpawn) {
                this.bunker.rightSpawn = Game.getObjectById(this.bunker.rightSpawn.id);
            }
        }
        this.roadLogistics.refresh();
        this.abathur.refresh();
    }
    /* Instantiate and associate virtual colony components to group similar structures together */
    registerHiveClusters() {
        this.hiveClusters = [];
        // Instantiate the command center if there is storage in the room - this must be done first!
        if (this.stage > ColonyStage.Larva) {
            this.commandCenter = new CommandCenter(this, this.storage);
        }
        // Instantiate the hatchery - the incubation directive assignes hatchery to incubator's hatchery if none exists
        if (this.spawns[0]) {
            this.hatchery = new Hatchery(this, this.spawns[0]);
        }
        // Instantiate evolution chamber once there are three labs all in range 2 of each other
        if (this.terminal && _.filter(this.labs, lab => _.all(this.labs, otherLab => lab.pos.inRangeTo(otherLab, 2))).length >= 3) {
            this.evolutionChamber = new EvolutionChamber(this, this.terminal);
        }
        // Instantiate the upgradeSite
        this.upgradeSite = new UpgradeSite(this, this.controller);
        // Instantiate spore crawlers to wrap towers
        if (this.towers[0]) {
            this.sporeCrawler = new SporeCrawler(this, this.towers[0]);
        }
        // Reverse the hive clusters for correct order for init() and run()
        this.hiveClusters.reverse();
    }
    refreshHiveClusters() {
        for (let i = this.hiveClusters.length - 1; i >= 0; i--) {
            this.hiveClusters[i].refresh();
        }
    }
    /* Instantiate all overlords for the colony */
    spawnMoarOverlords() {
        this.overlords = {
            default: new DefaultOverlord(this),
            work: new WorkerOverlord(this),
            logistics: new TransportOverlord(this),
        };
        if (!this.observer) {
            this.overlords.scout = new RandomWalkerScoutOverlord(this);
        }
        for (let hiveCluster of this.hiveClusters) {
            hiveCluster.spawnMoarOverlords();
        }
    }
    getCreepsByRole(roleName) {
        return this.creepsByRole[roleName] || [];
    }
    getZergByRole(roleName) {
        return _.map(this.getCreepsByRole(roleName), creep => Overmind.zerg[creep.name]);
    }
    /* Summarizes the total of all resources in colony store structures, labs, and some creeps */
    getAllAssets(verbose = false) {
        // if (this.name == 'E8S45') verbose = true; // 18863
        // Include storage structures and manager carry
        let stores = _.map(_.compact([this.storage, this.terminal]), s => s.store);
        let creepCarriesToInclude = _.map(this.creeps, creep => creep.carry);
        let allAssets = mergeSum([...stores, ...creepCarriesToInclude]);
        // Include lab amounts
        for (let lab of this.labs) {
            if (lab.mineralType) {
                if (!allAssets[lab.mineralType]) {
                    allAssets[lab.mineralType] = 0;
                }
                allAssets[lab.mineralType] += lab.mineralAmount;
            }
        }
        if (verbose)
            log.debug(`${this.room.print} assets: ` + JSON.stringify(allAssets));
        return allAssets;
    }
    init() {
        _.forEach(this.hiveClusters, hiveCluster => hiveCluster.init()); // Initialize each hive cluster
        this.roadLogistics.init(); // Initialize the road network
        this.linkNetwork.init(); // Initialize link network
        this.roomPlanner.init(); // Initialize the room planner
        if (Game.time % EXPANSION_EVALUATION_FREQ == 5 * this.id) { // Re-evaluate expansion data if needed
            ExpansionPlanner.refreshExpansionData(this);
        }
    }
    run() {
        _.forEach(this.hiveClusters, hiveCluster => hiveCluster.run()); // Run each hive cluster
        this.linkNetwork.run(); // Run the link network
        this.roadLogistics.run(); // Run the road network
        this.roomPlanner.run(); // Run the room planner
        this.stats(); // Log stats per tick
    }
    stats() {
        if (Game.time % LOG_STATS_INTERVAL == 0) {
            // Log energy and rcl
            Stats.log(`colonies.${this.name}.storage.energy`, this.storage ? this.storage.energy : undefined);
            Stats.log(`colonies.${this.name}.rcl.level`, this.controller.level);
            Stats.log(`colonies.${this.name}.rcl.progress`, this.controller.progress);
            Stats.log(`colonies.${this.name}.rcl.progressTotal`, this.controller.progressTotal);
            // Log average miningSite usage and uptime and estimated colony energy income
            let numSites = _.keys(this.miningSites).length;
            let avgDowntime = _.sum(this.miningSites, site => site.memory.stats.downtime) / numSites;
            let avgUsage = _.sum(this.miningSites, site => site.memory.stats.usage) / numSites;
            let energyInPerTick = _.sum(this.miningSites, site => site.overlords.mine.energyPerTick * site.memory.stats.usage);
            Stats.log(`colonies.${this.name}.miningSites.avgDowntime`, avgDowntime);
            Stats.log(`colonies.${this.name}.miningSites.avgUsage`, avgUsage);
            Stats.log(`colonies.${this.name}.miningSites.energyInPerTick`, energyInPerTick);
            Stats.log(`colonies.${this.name}.assets`, this.assets);
            // Log defensive properties
            Stats.log(`colonies.${this.name}.defcon`, this.defcon);
            let avgBarrierHits = _.sum(this.room.barriers, barrier => barrier.hits) / this.room.barriers.length;
            Stats.log(`colonies.${this.name}.avgBarrierHits`, avgBarrierHits);
        }
    }
    defconReport() {
        // let safeOutposts = _.filter(this.outposts, room => !!room && room.dangerousHostiles.length == 0);
        // let stringReport: string[] = [
        // 	`DEFCON: ${this.defcon}  Safe outposts: ${safeOutposts.length}/${this.outposts.length}`,
        // 	`Creep usage for ${colony.name}:`];
    }
    drawCreepReport(coord) {
        let { x, y } = coord;
        const roledata = Overmind.overseer.getCreepReport(this);
        const tablePos = new RoomPosition(x, y, this.room.name);
        y = Visualizer.infoBox(`${this.name} Creeps`, roledata, tablePos, 7);
        return { x, y };
    }
    visuals() {
        let x = 1;
        let y = 11.5;
        let coord;
        coord = this.drawCreepReport({ x, y });
        x = coord.x;
        y = coord.y;
        for (let hiveCluster of _.compact([this.hatchery, this.commandCenter, this.evolutionChamber])) {
            coord = hiveCluster.visuals({ x, y });
            x = coord.x;
            y = coord.y;
        }
    }
};
Colony.settings = {
    remoteSourcesByLevel: {
        1: 1,
        2: 2,
        3: 3,
        4: 4,
        5: 5,
        6: 6,
        7: 7,
        8: 9,
    },
    maxSourceDistance: 100
};
Colony = __decorate([
    profile,
    assimilationLocked
], Colony);

/* Road planner: sensibly builds road networks around colonies */
var RoadPlanner_1;
const PLAIN_COST = 3;
const SWAMP_COST = 4;
const WALL_COST = 15 * PLAIN_COST;
const EXISTING_PATH_COST = PLAIN_COST - 1;
let memoryDefaults = {
    roadLookup: {},
    roadCoverage: 0.0,
    roadCoverages: {}
};
let RoadPlanner = RoadPlanner_1 = class RoadPlanner {
    constructor(roomPlanner) {
        this.roomPlanner = roomPlanner;
        this.colony = roomPlanner.colony;
        this.memory = Mem.wrap(this.colony.memory, 'roadPlanner', memoryDefaults);
        this.costMatrices = {};
        this.roadPositions = [];
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'roadPlanner', memoryDefaults);
        this.costMatrices = {};
        this.roadPositions = [];
    }
    get roadCoverage() {
        return this.memory.roadCoverage;
    }
    recomputeRoadCoverages(storagePos) {
        // Compute coverage for each path
        for (let destination of this.colony.destinations) {
            let destName = destination.pos.name;
            if (!this.memory.roadCoverages[destName] || Game.time > this.memory.roadCoverages[destName].exp) {
                log.debug(`Recomputing road coverage from ${storagePos.print} to ${destination.pos.print}...`);
                let roadCoverage = this.computeRoadCoverage(storagePos, destination.pos);
                if (roadCoverage != undefined) {
                    // Set expiration to be longer if road is nearly complete
                    let expiration = roadCoverage.roadCount / roadCoverage.length >= 0.75
                        ? getCacheExpiration(RoadPlanner_1.settings.recomputeCoverageInterval)
                        : getCacheExpiration(3 * RoadPlanner_1.settings.recomputeCoverageInterval);
                    this.memory.roadCoverages[destName] = {
                        roadCount: roadCoverage.roadCount,
                        length: roadCoverage.length,
                        exp: expiration
                    };
                    log.debug(`Coverage: ${JSON.stringify(roadCoverage)}`);
                }
                else {
                    if (this.memory.roadCoverages[destName]) {
                        // if you already have some data, use it for a little while
                        this.memory.roadCoverages[destName].exp += 200;
                    }
                    else {
                        // otherwise put in a placeholder
                        this.memory.roadCoverages[destName] = {
                            roadCount: 0,
                            length: 1,
                            exp: Game.time + 100
                        };
                    }
                }
            }
        }
        // Store the aggregate roadCoverage score
        let totalRoadCount = 0;
        let totalPathLength = 0;
        for (let destName in this.memory.roadCoverages) {
            let { roadCount, length, exp } = this.memory.roadCoverages[destName];
            totalRoadCount += roadCount;
            totalPathLength += length;
        }
        this.memory.roadCoverage = totalRoadCount / totalPathLength;
    }
    computeRoadCoverage(storagePos, destination) {
        let ret = Pathing.findPath(storagePos, destination, { terrainCosts: { plainCost: 2, swampCost: 10 } });
        let path = ret.path;
        let roomNames = _.unique(_.map(path, pos => pos.roomName));
        // If you have vision or cached vision of the room
        if (_.all(roomNames, roomName => Game.rooms[roomName] || $.costMatrixRecall(roomName, MatrixTypes.default))) {
            let roadCount = 0;
            for (let pos of path) {
                if (Game.rooms[pos.roomName]) {
                    if (pos.lookForStructure(STRUCTURE_ROAD)) {
                        roadCount++;
                    }
                }
                else {
                    const mat = $.costMatrixRecall(pos.roomName, MatrixTypes.default);
                    if (mat) {
                        if (mat.get(pos.x, pos.y) == 1) {
                            roadCount++;
                        }
                    }
                    else { // shouldn't happen
                        log.warning(`No vision or recalled cost matrix in room ${pos.roomName}! (Why?)`);
                    }
                }
            }
            return { roadCount: roadCount, length: path.length };
        }
    }
    recalculateRoadNetwork(storagePos, obstacles) {
        this.buildRoadNetwork(storagePos, obstacles);
        this.finalize();
    }
    // Connect commandCenter to hatchery, upgradeSites, and all miningSites, and place containers
    buildRoadNetwork(storagePos, obstacles) {
        this.costMatrices = {};
        this.roadPositions = [];
        let destinations = _.sortBy(this.colony.destinations, destination => destination.order);
        // Connect commandCenter to each destination in colony
        for (let destination of destinations) {
            this.planRoad(storagePos, destination.pos, obstacles);
        }
        this.formatRoadPositions();
    }
    // Plan a road between two locations avoiding a list of planned obstacles; pos1 should be storage for best results
    planRoad(pos1, pos2, obstacles) {
        // Find the shortest path, preferentially stepping on tiles with road routing flags on them
        let roadPath = this.generateRoadPath(pos1, pos2, obstacles);
        if (roadPath) {
            this.roadPositions = this.roadPositions.concat(roadPath);
        }
    }
    generateRoadPlanningCostMatrix(roomName, obstacles) {
        let matrix = new PathFinder.CostMatrix();
        const terrain = Game.map.getRoomTerrain(roomName);
        for (let y = 0 + 1; y < 50 - 1; ++y) {
            for (let x = 0 + 1; x < 50 - 1; ++x) {
                switch (terrain.get(x, y)) {
                    case TERRAIN_MASK_SWAMP:
                        matrix.set(x, y, SWAMP_COST);
                        break;
                    case TERRAIN_MASK_WALL:
                        matrix.set(x, y, WALL_COST);
                        break;
                    default: // plain
                        matrix.set(x, y, PLAIN_COST);
                        break;
                }
            }
        }
        for (let pos of obstacles) {
            if (pos.roomName == roomName) {
                matrix.set(pos.x, pos.y, 0xff);
            }
        }
        const room = Game.rooms[roomName];
        if (room) {
            let impassibleStructures = [];
            _.forEach(room.find(FIND_STRUCTURES), (s) => {
                if (!s.isWalkable) {
                    impassibleStructures.push(s);
                }
            });
            _.forEach(impassibleStructures, s => matrix.set(s.pos.x, s.pos.y, 0xff));
            // Set passability of construction sites
            _.forEach(room.find(FIND_MY_CONSTRUCTION_SITES), (site) => {
                if (!site.isWalkable) {
                    matrix.set(site.pos.x, site.pos.y, 0xff);
                }
            });
        }
        return matrix;
    }
    /* Generates a road path and modifies cost matrices to encourage merging with future roads */
    generateRoadPath(origin, destination, obstacles) {
        let callback = (roomName) => {
            if (!this.colony.roomNames.includes(roomName)) { // only route through colony rooms
                return false;
            }
            if (Pathing.shouldAvoid(roomName) && roomName != origin.roomName && roomName != destination.roomName) {
                return false;
            }
            if (!this.costMatrices[roomName]) {
                this.costMatrices[roomName] = this.generateRoadPlanningCostMatrix(roomName, obstacles);
            }
            return this.costMatrices[roomName];
        };
        let ret = PathFinder.search(origin, { pos: destination, range: 1 }, { roomCallback: callback, maxOps: 40000 });
        if (ret.incomplete) {
            log.warning(`Roadplanner for ${this.colony.print}: could not plan road path!`);
            return;
        }
        // Reduce the cost of planned paths to encourage road overlap for future pathing
        if (RoadPlanner_1.settings.encourageRoadMerging) {
            for (let i of _.range(ret.path.length)) {
                let pos = ret.path[i];
                if (i % 2 == 0 && this.costMatrices[pos.roomName] && !pos.isEdge) {
                    this.costMatrices[pos.roomName].set(pos.x, pos.y, EXISTING_PATH_COST);
                }
            }
        }
        // Return the pathfinder results
        return ret.path;
    }
    /* Ensure that the roads doesn't overlap with roads from this.map and that the positions are unique */
    formatRoadPositions() {
        // Make road position list unique
        this.roadPositions = _.unique(this.roadPositions);
        // Remove roads located on exit tiles
        _.remove(this.roadPositions, pos => pos.isEdge);
        // Remove any roads duplicated in this.map
        let roomPlannerRoads = this.roomPlanner.plannedStructurePositions(STRUCTURE_ROAD);
        if (roomPlannerRoads != undefined) {
            _.remove(this.roadPositions, pos => roomPlannerRoads.includes(pos));
        }
    }
    /* Write everything to memory after roomPlanner is closed */
    finalize() {
        // Collect all roads from this and from room planner
        let roomPlannerRoads;
        if (_.keys(this.roomPlanner.map).length > 0) { // use active map
            roomPlannerRoads = this.roomPlanner.map[STRUCTURE_ROAD];
        }
        else { // retrieve from memory
            if (this.roomPlanner.memory.bunkerData && this.roomPlanner.memory.bunkerData.anchor) {
                let layout = this.roomPlanner.getStructureMapForBunkerAt(this.roomPlanner.memory.bunkerData.anchor);
                roomPlannerRoads = layout[STRUCTURE_ROAD];
            }
            else if (this.roomPlanner.memory.mapsByLevel) {
                roomPlannerRoads = _.map(this.roomPlanner.memory.mapsByLevel[8][STRUCTURE_ROAD], protoPos => derefRoomPosition(protoPos));
            }
            else {
                log.error(`RoadPlanner@${this.colony.room.print}: could not get road positions from room planner!`);
                roomPlannerRoads = [];
            }
        }
        let allRoadPos = _.compact(this.roadPositions.concat(roomPlannerRoads));
        // Encode the coordinates of the road as keys in a truthy hash table for fast lookup
        this.memory.roadLookup = {};
        for (let pos of allRoadPos) {
            if (!this.memory.roadLookup[pos.roomName])
                this.memory.roadLookup[pos.roomName] = {};
            this.memory.roadLookup[pos.roomName][pos.coordName] = true;
        }
    }
    init() {
    }
    static shouldBuild(structureType, pos) {
        if (!pos.room)
            return false;
        let buildings = _.filter(pos.lookFor(LOOK_STRUCTURES), s => s && s.structureType == structureType);
        let sites = pos.lookFor(LOOK_CONSTRUCTION_SITES);
        if (!buildings || buildings.length == 0) {
            if (!sites || sites.length == 0) {
                return true;
            }
        }
        return false;
    }
    /* Create construction sites for any buildings that need to be built */
    buildMissing() {
        // Max buildings that can be placed each tick
        let count = RoomPlanner.settings.maxSitesPerColony - this.colony.constructionSites.length;
        // Build missing roads
        let roadPositions = [];
        for (let roomName in this.memory.roadLookup) {
            for (let coords of _.keys(this.memory.roadLookup[roomName])) {
                let [x, y] = coords.split(':');
                roadPositions.push(new RoomPosition(parseInt(x, 10), parseInt(y, 10), roomName));
            }
        }
        let origin = (this.colony.storage || this.colony.hatchery || this.colony).pos;
        roadPositions = _.sortBy(roadPositions, pos => pos.getMultiRoomRangeTo(origin));
        for (let pos of roadPositions) {
            if (count > 0 && RoomPlanner.canBuild(STRUCTURE_ROAD, pos)) {
                let ret = pos.createConstructionSite(STRUCTURE_ROAD);
                if (ret != OK) {
                    log.warning(`${this.colony.name}: couldn't create road site at ${pos.print}. Result: ${ret}`);
                }
                else {
                    count--;
                }
            }
        }
    }
    /* Quick lookup for if a road should be in this position. Roads returning false won't be maintained. */
    roadShouldBeHere(pos) {
        // Initial migration code, can delete later
        if (this.memory.roadLookup[pos.roomName]) {
            return this.memory.roadLookup[pos.roomName][pos.coordName];
        }
        return false;
    }
    run() {
        if (this.roomPlanner.active) {
            if (this.roomPlanner.storagePos) {
                this.buildRoadNetwork(this.roomPlanner.storagePos, this.roomPlanner.getObstacles());
            }
            this.visuals();
        }
        else {
            // Once in a blue moon, recalculate the entire network and write to memory to keep it up to date
            if (Game.time % RoadPlanner_1.settings.recalculateRoadNetworkInterval == this.colony.id) {
                if (this.roomPlanner.storagePos) {
                    this.recalculateRoadNetwork(this.roomPlanner.storagePos, this.roomPlanner.getObstacles());
                }
            }
            // Recompute coverage to destinations
            if (Game.time % getAllColonies().length == this.colony.id && this.roomPlanner.storagePos) {
                this.recomputeRoadCoverages(this.roomPlanner.storagePos);
            }
            // Build missing roads
            if (this.colony.level >= RoadPlanner_1.settings.buildRoadsAtRCL && this.roomPlanner.shouldRecheck(3)) {
                this.buildMissing();
            }
        }
    }
    visuals() {
        // Draw the map
        Visualizer.drawRoads(this.roadPositions);
    }
};
RoadPlanner.settings = {
    encourageRoadMerging: true,
    recalculateRoadNetworkInterval: onPublicServer() ? 3000 : 1000,
    recomputeCoverageInterval: onPublicServer() ? 1000 : 500,
    buildRoadsAtRCL: 4,
};
RoadPlanner = RoadPlanner_1 = __decorate([
    profile
], RoadPlanner);

/**
 * Code for calculating the minCut in a room, written by Saruss,
 * adapted for Typescript and flexible room subsets by Chobobobo,
 * modified and debugged by Muon.
 */
const UNWALKABLE = -10;
const RANGE_MODIFIER = 1; // this parameter sets the scaling of weights to prefer walls closer protection bounds
const RANGE_PADDING = 3; // max range to reduce weighting; RANGE_MODIFIER * RANGE_PADDING must be < PROTECTED
const NORMAL = 0;
const PROTECTED = 10;
const CANNOT_BUILD = 20;
const EXIT = 30;
class Graph {
    constructor(totalVertices) {
        this.totalVertices = totalVertices;
        this.level = Array(totalVertices);
        // An array of edges for each vertex
        this.edges = Array(totalVertices).fill(0).map((x) => []);
    }
    /**
     * Create a new edge in the graph as well as a corresponding reverse edge on the residual graph
     * @param from - vertex edge starts at
     * @param to - vertex edge leads to
     * @param capacity - max flow capacity for this edge
     */
    newEdge(from, to, capacity) {
        // Normal forward Edge
        this.edges[from].push({ to, resEdge: this.edges[to].length, capacity, flow: 0 });
        // reverse Edge for Residual Graph
        this.edges[to].push({ to: from, resEdge: this.edges[from].length - 1, capacity: 0, flow: 0 });
    }
    /**
     * Uses Breadth First Search to see if a path exists to the vertex 'to' and generate the level graph
     * @param from - vertex to start from
     * @param to - vertex to try and reach
     */
    createLevelGraph(from, to) {
        if (to >= this.totalVertices) {
            return false;
        }
        this.level.fill(-1); // reset old levels
        this.level[from] = 0;
        const q = []; // queue with s as starting point
        q.push(from);
        let u = 0;
        let edge = null;
        while (q.length) {
            u = q.shift();
            for (edge of this.edges[u]) {
                if (this.level[edge.to] < 0 && edge.flow < edge.capacity) {
                    this.level[edge.to] = this.level[u] + 1;
                    q.push(edge.to);
                }
            }
        }
        return this.level[to] >= 0; // return if theres a path, no level, no path!
    }
    /**
     * Depth First Search-like: send flow at along path from from->to recursively while increasing the level of the
     * visited vertices by one
     * @param start - the vertex to start at
     * @param end - the vertex to try and reach
     * @param targetFlow - the amount of flow to try and achieve
     * @param count - keep track of which vertices have been visited so we don't include them twice
     */
    calcFlow(start, end, targetFlow, count) {
        if (start === end) { // Sink reached , abort recursion
            return targetFlow;
        }
        let edge;
        let flowTillHere = 0;
        let flowToT = 0;
        while (count[start] < this.edges[start].length) { // Visit all edges of the vertex one after the other
            edge = this.edges[start][count[start]];
            if (this.level[edge.to] === this.level[start] + 1 && edge.flow < edge.capacity) {
                // Edge leads to Vertex with a level one higher, and has flow left
                flowTillHere = Math.min(targetFlow, edge.capacity - edge.flow);
                flowToT = this.calcFlow(edge.to, end, flowTillHere, count);
                if (flowToT > 0) {
                    edge.flow += flowToT; // Add Flow to current edge
                    // subtract from reverse Edge -> Residual Graph neg. Flow to use backward direction of BFS/DFS
                    this.edges[edge.to][edge.resEdge].flow -= flowToT;
                    return flowToT;
                }
            }
            count[start]++;
        }
        return 0;
    }
    /**
     * Uses Breadth First Search to find the vertices in the minCut for the graph
     * - Must call calcMinCut first to prepare the graph
     * @param from - the vertex to start from
     */
    getMinCut(from) {
        const eInCut = [];
        this.level.fill(-1);
        this.level[from] = 1;
        const q = [];
        q.push(from);
        let u = 0;
        let edge;
        while (q.length) {
            u = q.shift();
            for (edge of this.edges[u]) {
                if (edge.flow < edge.capacity) {
                    if (this.level[edge.to] < 1) {
                        this.level[edge.to] = 1;
                        q.push(edge.to);
                    }
                }
                if (edge.flow === edge.capacity && edge.capacity > 0) { // blocking edge -> could be in min cut
                    eInCut.push({ to: edge.to, unreachable: u });
                }
            }
        }
        const minCut = [];
        let cutEdge;
        for (cutEdge of eInCut) {
            if (this.level[cutEdge.to] === -1) {
                // Only edges which are blocking and lead to the sink from unreachable vertices are in the min cut
                minCut.push(cutEdge.unreachable);
            }
        }
        return minCut;
    }
    /**
     * Calculates min-cut graph using Dinic's Algorithm.
     * use getMinCut to get the actual verticies in the minCut
     * @param source - Source vertex
     * @param sink - Sink vertex
     */
    calcMinCut(source, sink) {
        if (source === sink) {
            return -1;
        }
        let ret = 0;
        let count = [];
        let flow = 0;
        while (this.createLevelGraph(source, sink)) {
            count = Array(this.totalVertices + 1).fill(0);
            do {
                flow = this.calcFlow(source, sink, Number.MAX_VALUE, count);
                if (flow > 0) {
                    ret += flow;
                }
            } while (flow);
        }
        return ret;
    }
}
/**
 * An Array with Terrain information: -1 not usable, 2 Sink (Leads to Exit)
 * @param room - the room to generate the terrain map from
 */
function get2DArray(roomName, bounds = { x1: 0, y1: 0, x2: 49, y2: 49 }) {
    const room2D = Array(50).fill(NORMAL).map((d) => Array(50).fill(NORMAL)); // Array for room tiles
    let x;
    let y;
    const terrain = Game.map.getRoomTerrain(roomName);
    for (x = bounds.x1; x <= bounds.x2; x++) {
        for (y = bounds.y1; y <= bounds.y2; y++) {
            if (terrain.get(x, y) === TERRAIN_MASK_WALL) {
                room2D[x][y] = UNWALKABLE; // Mark unwalkable
            }
            else if (x === bounds.x1 || y === bounds.y1 || x === bounds.x2 || y === bounds.y2) {
                room2D[x][y] = EXIT; // Mark exit tiles
            }
        }
    }
    // Marks tiles as unbuildable if they are proximate to exits
    for (y = bounds.y1 + 1; y <= bounds.y2 - 1; y++) {
        if (room2D[bounds.x1][y] === EXIT) {
            for (let dy of [-1, 0, 1]) {
                if (room2D[bounds.x1 + 1][y + dy] !== UNWALKABLE) {
                    room2D[bounds.x1 + 1][y + dy] = CANNOT_BUILD;
                }
            }
        }
        if (room2D[bounds.x2][y] === EXIT) {
            for (let dy of [-1, 0, 1]) {
                if (room2D[bounds.x2 - 1][y + dy] !== UNWALKABLE) {
                    room2D[bounds.x2 - 1][y + dy] = CANNOT_BUILD;
                }
            }
        }
    }
    for (x = bounds.x1 + 1; x <= bounds.x2 - 1; x++) {
        if (room2D[x][bounds.y1] === EXIT) {
            for (let dx of [-1, 0, 1]) {
                if (room2D[x + dx][bounds.y1 + 1] !== UNWALKABLE) {
                    room2D[x + dx][bounds.y1 + 1] = CANNOT_BUILD;
                }
            }
        }
        if (room2D[x][bounds.y2] === EXIT) {
            for (let dx of [-1, 0, 1]) {
                if (room2D[x + dx][bounds.y2 - 1] !== UNWALKABLE) {
                    room2D[x + dx][bounds.y2 - 1] = CANNOT_BUILD;
                }
            }
        }
    }
    return room2D;
}
/**
 * Function to create Source, Sink, Tiles arrays: takes a rectangle-Array as input for Tiles that are to Protect
 * @param room - the room to consider
 * @param toProtect - the coordinates to protect inside the walls
 * @param bounds - the area to consider for the minCut
 */
function createGraph(roomName, toProtect, preferCloserBarriers = true, preferCloserBarrierLimit = Infinity, // ignore the toProtect[n] for n > this value
visualize = true, bounds = { x1: 0, y1: 0, x2: 49, y2: 49 }) {
    const visual = new RoomVisual(roomName);
    const roomArray = get2DArray(roomName, bounds);
    // For all Rectangles, set edges as source (to protect area) and area as unused
    let r;
    let x;
    let y;
    for (r of toProtect) {
        if (bounds.x1 >= bounds.x2 || bounds.y1 >= bounds.y2 ||
            bounds.x1 < 0 || bounds.y1 < 0 || bounds.x2 > 49 || bounds.y2 > 49) {
            return console.log('ERROR: Invalid bounds', JSON.stringify(bounds));
        }
        else if (r.x1 >= r.x2 || r.y1 >= r.y2) {
            return console.log('ERROR: Rectangle', JSON.stringify(r), 'invalid.');
        }
        else if (r.x1 < bounds.x1 || r.x2 > bounds.x2 || r.y1 < bounds.y1 || r.y2 > bounds.y2) {
            return console.log('ERROR: Rectangle', JSON.stringify(r), 'out of bounds:', JSON.stringify(bounds));
        }
        for (x = r.x1; x <= r.x2; x++) {
            for (y = r.y1; y <= r.y2; y++) {
                if (x === r.x1 || x === r.x2 || y === r.y1 || y === r.y2) {
                    if (roomArray[x][y] === NORMAL) {
                        roomArray[x][y] = PROTECTED;
                    }
                }
                else {
                    roomArray[x][y] = UNWALKABLE;
                }
            }
        }
    }
    // Preferentially weight closer tiles
    if (preferCloserBarriers) {
        for (r of _.take(toProtect, preferCloserBarrierLimit)) {
            let [xmin, xmax] = [Math.max(r.x1 - RANGE_PADDING, 0), Math.min(r.x2 + RANGE_PADDING, 49)];
            let [ymin, ymax] = [Math.max(r.y1 - RANGE_PADDING, 0), Math.min(r.y2 + RANGE_PADDING, 49)];
            for (x = xmin; x <= xmax; x++) {
                for (y = ymin; y <= ymax; y++) {
                    if (roomArray[x][y] >= NORMAL && roomArray[x][y] < PROTECTED) {
                        let x1range = Math.max(r.x1 - x, 0);
                        let x2range = Math.max(x - r.x2, 0);
                        let y1range = Math.max(r.y1 - y, 0);
                        let y2range = Math.max(y - r.y2, 0);
                        let rangeToBorder = Math.max(x1range, x2range, y1range, y2range);
                        let modifiedWeight = NORMAL + RANGE_MODIFIER * (RANGE_PADDING - rangeToBorder);
                        roomArray[x][y] = Math.max(roomArray[x][y], modifiedWeight);
                        if (visualize) {
                            visual.text(`${roomArray[x][y]}`, x, y);
                        }
                    }
                }
            }
        }
    }
    let max;
    // ********************** Visualization
    if (visualize) {
        for (x = bounds.x1; x <= bounds.x2; x++) {
            for (y = bounds.y1; y <= bounds.y2; y++) {
                if (roomArray[x][y] === UNWALKABLE) {
                    visual.circle(x, y, { radius: 0.5, fill: '#1b1b9f', opacity: 0.3 });
                }
                else if (roomArray[x][y] > UNWALKABLE && roomArray[x][y] < NORMAL) {
                    visual.circle(x, y, { radius: 0.5, fill: '#42cce8', opacity: 0.3 });
                }
                else if (roomArray[x][y] === NORMAL) {
                    visual.circle(x, y, { radius: 0.5, fill: '#bdb8b8', opacity: 0.3 });
                }
                else if (roomArray[x][y] > NORMAL && roomArray[x][y] < PROTECTED) {
                    visual.circle(x, y, { radius: 0.5, fill: '#9929e8', opacity: 0.3 });
                }
                else if (roomArray[x][y] === PROTECTED) {
                    visual.circle(x, y, { radius: 0.5, fill: '#e800c6', opacity: 0.3 });
                }
                else if (roomArray[x][y] === CANNOT_BUILD) {
                    visual.circle(x, y, { radius: 0.5, fill: '#e8000f', opacity: 0.3 });
                }
                else if (roomArray[x][y] === EXIT) {
                    visual.circle(x, y, { radius: 0.5, fill: '#000000', opacity: 0.3 });
                }
            }
        }
    }
    // initialise graph
    // possible 2*50*50 +2 (st) Vertices (Walls etc set to unused later)
    const g = new Graph(2 * 50 * 50 + 2);
    const infini = Number.MAX_VALUE;
    const surr = [[0, -1], [-1, -1], [-1, 0], [-1, 1], [0, 1], [1, 1], [1, 0], [1, -1]];
    // per Tile (0 in Array) top + bot with edge of c=1 from top to bott  (use every tile once!)
    // infini edge from bot to top vertices of adjacent tiles if they not protected (array =1)
    // (no reverse edges in normal graph)
    // per prot. Tile (1 in array) Edge from source to this tile with infini cap.
    // per exit Tile (2in array) Edge to sink with infini cap.
    // source is at  pos 2*50*50, sink at 2*50*50+1 as first tile is 0,0 => pos 0
    // top vertices <-> x,y : v=y*50+x   and x= v % 50  y=v/50 (math.floor?)
    // bot vertices <-> top + 2500
    const source = 2 * 50 * 50;
    const sink = 2 * 50 * 50 + 1;
    let top = 0;
    let bot = 0;
    let dx = 0;
    let dy = 0;
    // max = 49;
    const baseCapacity = 10;
    const modifyWeight = preferCloserBarriers ? 1 : 0;
    for (x = bounds.x1 + 1; x < bounds.x2; x++) {
        for (y = bounds.y1 + 1; y < bounds.y2; y++) {
            top = y * 50 + x;
            bot = top + 2500;
            if (roomArray[x][y] >= NORMAL && roomArray[x][y] <= PROTECTED) {
                if (roomArray[x][y] >= NORMAL && roomArray[x][y] < PROTECTED) {
                    g.newEdge(top, bot, baseCapacity - modifyWeight * roomArray[x][y]); // add surplus weighting
                }
                else if (roomArray[x][y] === PROTECTED) { // connect this to the source
                    g.newEdge(source, top, infini);
                    g.newEdge(top, bot, baseCapacity - modifyWeight * RANGE_PADDING * RANGE_MODIFIER);
                }
                for (let i = 0; i < 8; i++) { // attach adjacent edges
                    dx = x + surr[i][0];
                    dy = y + surr[i][1];
                    if ((roomArray[dx][dy] >= NORMAL && roomArray[dx][dy] < PROTECTED)
                        || roomArray[dx][dy] === CANNOT_BUILD) {
                        g.newEdge(bot, dy * 50 + dx, infini);
                    }
                }
            }
            else if (roomArray[x][y] === CANNOT_BUILD) { // near Exit
                g.newEdge(top, sink, infini);
            }
        }
    } // graph finished
    return g;
}
/**
 * Main function to be called by user: calculate min cut tiles from room using rectangles as protected areas
 * @param room - the room to use
 * @param rectangles - the areas to protect, defined as rectangles
 * @param bounds - the area to be considered for the minCut
 */
function getCutTiles(roomName, toProtect, preferCloserBarriers = true, preferCloserBarrierLimit = Infinity, visualize = true, bounds = { x1: 0, y1: 0, x2: 49, y2: 49 }) {
    const graph = createGraph(roomName, toProtect, preferCloserBarriers, preferCloserBarrierLimit, visualize, bounds);
    if (!graph) {
        return [];
    }
    let x;
    let y;
    const source = 2 * 50 * 50; // Position Source / Sink in Room-Graph
    const sink = 2 * 50 * 50 + 1;
    const count = graph.calcMinCut(source, sink);
    // console.log('Number of Tiles in Cut:', count);
    const positions = [];
    if (count > 0) {
        const cutVertices = graph.getMinCut(source);
        let v;
        for (v of cutVertices) {
            // x= vertex % 50  y=v/50 (math.floor?)
            x = v % 50;
            y = Math.floor(v / 50);
            positions.push({ x, y });
        }
    }
    // Visualise Result
    if (positions.length > 0) {
        const visual = new RoomVisual(roomName);
        for (let i = positions.length - 1; i >= 0; i--) {
            visual.circle(positions[i].x, positions[i].y, { radius: 0.5, fill: '#ff7722', opacity: 0.9 });
        }
    }
    else {
        return [];
    }
    const wholeRoom = bounds.x1 === 0 && bounds.y1 === 0 && bounds.x2 === 49 && bounds.y2 === 49;
    return wholeRoom ? positions : pruneDeadEnds(roomName, positions);
}
/**
 * Removes unnecessary tiles if they are blocking the path to a dead end
 * Useful if minCut has been run on a subset of the room
 * @param roomName - Room to work in
 * @param cutTiles - Array of tiles which are in the minCut
 */
function pruneDeadEnds(roomName, cutTiles) {
    // Get Terrain and set all cut-tiles as unwalkable
    const roomArray = get2DArray(roomName);
    let tile;
    for (tile of cutTiles) {
        roomArray[tile.x][tile.y] = UNWALKABLE;
    }
    // Floodfill from exits: save exit tiles in array and do a BFS-like search
    const unvisited = [];
    let y;
    let x;
    for (y = 0; y < 49; y++) {
        if (roomArray[0][y] === EXIT) {
            console.log('prune: toExit', 0, y);
            unvisited.push(50 * y);
        }
        if (roomArray[49][y] === EXIT) {
            console.log('prune: toExit', 49, y);
            unvisited.push(50 * y + 49);
        }
    }
    for (x = 0; x < 49; x++) {
        if (roomArray[x][0] === EXIT) {
            console.log('prune: toExit', x, 0);
            unvisited.push(x);
        }
        if (roomArray[x][49] === EXIT) {
            console.log('prune: toExit', x, 49);
            unvisited.push(2450 + x); // 50*49=2450
        }
    }
    // Iterate over all unvisited EXIT tiles and mark neigbours as EXIT tiles if walkable, add to unvisited
    const surr = [[0, -1], [-1, -1], [-1, 0], [-1, 1], [0, 1], [1, 1], [1, 0], [1, -1]];
    let currPos;
    let dx;
    let dy;
    while (unvisited.length > 0) {
        currPos = unvisited.pop();
        x = currPos % 50;
        y = Math.floor(currPos / 50);
        for (let i = 0; i < 8; i++) {
            dx = x + surr[i][0];
            dy = y + surr[i][1];
            if (dx < 0 || dx > 49 || dy < 0 || dy > 49) {
                continue;
            }
            if ((roomArray[dx][dy] >= NORMAL && roomArray[dx][dy] < PROTECTED)
                || roomArray[dx][dy] === CANNOT_BUILD) {
                unvisited.push(50 * dy + dx);
                roomArray[dx][dy] = EXIT;
            }
        }
    }
    // Remove min-Cut-Tile if there is no EXIT reachable by it
    let leadsToExit;
    const validCut = [];
    for (tile of cutTiles) {
        leadsToExit = false;
        for (let j = 0; j < 8; j++) {
            dx = tile.x + surr[j][0];
            dy = tile.y + surr[j][1];
            if (roomArray[dx][dy] === EXIT) {
                leadsToExit = true;
            }
        }
        if (leadsToExit) {
            validCut.push(tile);
        }
    }
    return validCut;
}
/**
 * Example function: demonstrates how to get a min cut with 2 rectangles, which define a "to protect" area
 * @param roomName - the name of the room to use for the test, must be visible
 */
function testMinCut(colonyName, preferCloserBarriers = true) {
    let colony = Overmind.colonies[colonyName];
    if (!colony) {
        return `No colony: ${colonyName}`;
    }
    let cpu = Game.cpu.getUsed();
    // Rectangle Array, the Rectangles will be protected by the returned tiles
    const rectArray = [];
    let padding = 3;
    if (colony.hatchery) {
        let { x, y } = colony.hatchery.pos;
        let [x1, y1] = [Math.max(x - 5 - padding, 0), Math.max(y - 4 - padding, 0)];
        let [x2, y2] = [Math.min(x + 5 + padding, 49), Math.min(y + 6 + padding, 49)];
        rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
    }
    if (colony.commandCenter) {
        let { x, y } = colony.commandCenter.pos;
        let [x1, y1] = [Math.max(x - 3 - padding, 0), Math.max(y - 0 - padding, 0)];
        let [x2, y2] = [Math.min(x + 0 + padding, 49), Math.min(y + 5 + padding, 49)];
        rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
    }
    if (colony.upgradeSite) {
        let { x, y } = colony.upgradeSite.pos;
        let [x1, y1] = [Math.max(x - 1, 0), Math.max(y - 1, 0)];
        let [x2, y2] = [Math.min(x + 1, 49), Math.min(y + 1, 49)];
        rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
    }
    // Get Min cut
    const positions = getCutTiles(colonyName, rectArray, preferCloserBarriers, 2); // Positions is an array where to build walls/ramparts
    // Test output
    // console.log('Positions returned', positions.length);
    cpu = Game.cpu.getUsed() - cpu;
    // console.log('Needed', cpu, ' cpu time');
    log.info(`preferCloserBarriers = ${preferCloserBarriers}; positions returned: ${positions.length};` +
        ` CPU time: ${cpu}`);
    return 'Finished';
}
/**
 * Example function: demonstrates how to get a min cut with 2 rectangles, which define a "to protect" area
 * while considering a subset of the larger room.
 * @param roomName - the name of the room to use for the test, must be visible
 */
function testMinCutSubset(colonyName) {
    let colony = Overmind.colonies[colonyName];
    if (!colony) {
        return `No colony: ${colonyName}`;
    }
    let cpu = Game.cpu.getUsed();
    // Rectangle Array, the Rectangles will be protected by the returned tiles
    const rectArray = [];
    let padding = 3;
    if (colony.hatchery) {
        let { x, y } = colony.hatchery.pos;
        rectArray.push({ x1: x - 5 - padding, y1: y - 4 - padding, x2: x + 5 + padding, y2: y + 6 + padding });
    }
    if (colony.commandCenter) {
        let { x, y } = colony.commandCenter.pos;
        rectArray.push({ x1: x - 3 - padding, y1: y - 0 - padding, x2: x + 0 + padding, y2: y + 5 + padding });
    }
    // Get Min cut, returns the positions where ramparts/walls need to be
    const positions = getCutTiles(colonyName, rectArray, true, Infinity, true, { x1: 5, y1: 5, x2: 44, y2: 44 });
    // Test output
    console.log('Positions returned', positions.length);
    cpu = Game.cpu.getUsed() - cpu;
    console.log('Needed', cpu, ' cpu time');
    return 'Finished';
}

var BarrierPlanner_1;
let memoryDefaults$1 = {
    barrierLookup: {},
};
let BarrierPlanner = BarrierPlanner_1 = class BarrierPlanner {
    constructor(roomPlanner) {
        this.roomPlanner = roomPlanner;
        this.colony = roomPlanner.colony;
        this.memory = Mem.wrap(this.colony.memory, 'barrierPlanner', memoryDefaults$1);
        this.barrierPositions = [];
    }
    refresh() {
        this.memory = Mem.wrap(this.colony.memory, 'barrierPlanner', memoryDefaults$1);
        this.barrierPositions = [];
    }
    computeBunkerBarrierPositions(bunkerPos, upgradeSitePos) {
        let rectArray = [];
        let padding = BarrierPlanner_1.settings.padding;
        if (bunkerPos) {
            let { x, y } = bunkerPos;
            const r = BUNKER_RADIUS - 1;
            let [x1, y1] = [Math.max(x - r - padding, 0), Math.max(y - r - padding, 0)];
            let [x2, y2] = [Math.min(x + r + padding, 49), Math.min(y + r + padding, 49)];
            // Make sure you don't leave open walls
            x1 = minMax(x1, 3, 50 - 3);
            x2 = minMax(x2, 3, 50 - 3);
            y1 = minMax(y1, 3, 50 - 3);
            y2 = minMax(y2, 3, 50 - 3);
            rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
        }
        // Get Min cut
        let barrierCoords = getCutTiles(this.colony.name, rectArray, false, 2, false);
        let positions = _.map(barrierCoords, coord => new RoomPosition(coord.x, coord.y, this.colony.name));
        positions = positions.concat(upgradeSitePos.availableNeighbors(true));
        return positions;
    }
    computeBarrierPositions(hatcheryPos, commandCenterPos, upgradeSitePos) {
        let rectArray = [];
        let padding = BarrierPlanner_1.settings.padding;
        if (hatcheryPos) {
            let { x, y } = hatcheryPos;
            let [x1, y1] = [Math.max(x - 5 - padding, 0), Math.max(y - 4 - padding, 0)];
            let [x2, y2] = [Math.min(x + 5 + padding, 49), Math.min(y + 6 + padding, 49)];
            rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
        }
        if (commandCenterPos) {
            let { x, y } = commandCenterPos;
            let [x1, y1] = [Math.max(x - 3 - padding, 0), Math.max(y - 0 - padding, 0)];
            let [x2, y2] = [Math.min(x + 0 + padding, 49), Math.min(y + 5 + padding, 49)];
            rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
        }
        if (upgradeSitePos) {
            let { x, y } = upgradeSitePos;
            let [x1, y1] = [Math.max(x - 1, 0), Math.max(y - 1, 0)];
            let [x2, y2] = [Math.min(x + 1, 49), Math.min(y + 1, 49)];
            rectArray.push({ x1: x1, y1: y1, x2: x2, y2: y2 });
        }
        // Get Min cut
        let barrierCoords = getCutTiles(this.colony.name, rectArray, true, 2, false);
        return _.map(barrierCoords, coord => new RoomPosition(coord.x, coord.y, this.colony.name));
    }
    init() {
    }
    /* Write everything to memory after roomPlanner is closed */
    finalize() {
        this.memory.barrierLookup = {};
        if (this.barrierPositions.length == 0) {
            if (this.roomPlanner.bunkerPos) {
                this.barrierPositions = this.computeBunkerBarrierPositions(this.roomPlanner.bunkerPos, this.colony.controller.pos);
            }
            else if (this.roomPlanner.storagePos && this.roomPlanner.hatcheryPos) {
                this.barrierPositions = this.computeBarrierPositions(this.roomPlanner.hatcheryPos, this.roomPlanner.storagePos, this.colony.controll
