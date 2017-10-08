"use strict";
// Note: this entire script is a huge, somewhat fragile hack to get a svg of our figure with working hyperlinks
Object.defineProperty(exports, "__esModule", { value: true });
var FS = require("fs");
var inputFile = process.argv[2];
var array = FS.readFileSync(inputFile).toString().split("\n");
function isSelfClosingLink(line) {
    return /^<a.*\/>$/.test(line);
}
function isTranslationLink(line) {
    return /Qcert[.]Translation[.]/.test(line);
}
function isOptimLink(line) {
    return /Optim/.test(line);
}
function isPath(line) {
    return /\<path/.test(line);
}
function getColor(line) {
    var myArray = /stroke='([^']*)'/.exec(line);
    if (myArray != null)
        return myArray[1];
    else
        return '';
}
function addColor(array, i, color) {
    array[i] = array[i].replace("/>", " fill='" + color + "'/>");
}
function isTextual(line) {
    return /<\/?text/.test(line) || /<\/?tspan/.test(line);
}
function widen(array, i, offset) {
    var line = array[i];
    array[i] = "</a>";
    array.splice(i - offset, 0, line.replace("/>", ">"));
}
// first, let us remove duplicate link lines
for (var i = 0; i < array.length;) {
    var line = array[i];
    i++;
    if (isSelfClosingLink(line)) {
        for (; i < array.length && line === array[i]; i++) {
            array[i] = undefined;
        }
    }
}
array = array.filter(function (line) { return line !== undefined; });
// next, lets widen the links.
// for some reason, they are output as self closing tags at the end of the span they should contain
// so we move the beginning tag earlier so that it covers the desired span
for (var i = 0; i < array.length; i++) {
    var line = array[i];
    if (isSelfClosingLink(line)) {
        if (isTranslationLink(line) || isOptimLink(line)) {
            // for translation links, we move two lines (path statements) earlier
            if (i >= 2) {
                if (isPath(array[i - 1]) && isPath(array[i - 2])) {
                    var color = getColor(array[i - 2]);
                    console.error('line: ' + array[i - 2] + 'color: ' + color);
                    console.error('line: ' + array[i - 1]);
                    addColor(array, i - 1, color);
                    console.error('line: ' + array[i - 1]);
                    widen(array, i, 2);
                }
                i++;
            }
        }
        else {
            // for non-translation links, we move before any "textual" tags
            var prev = i - 1;
            while (prev > 0 && isTextual(array[prev])) {
                prev--;
            }
            prev++;
            widen(array, i, i - prev);
            i++;
        }
    }
}
// finally, lets rewrite all of our links so they target a new page
var fullSVG = array.join('\n');
var outputSVG = fullSVG.replace(/<a /g, "<a target='_top' ");
console.log(outputSVG);
