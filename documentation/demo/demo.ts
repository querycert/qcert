/// <reference path="./node_modules/qcert/libs/qcertJS.d.ts" />
/// <reference path="./lib/fabric.d.ts" />

// some types

interface PuzzleSides {
	left?:-1|0|1;
	top?:-1|0|1;
	right?:-1|0|1;
	bottom?:-1|0|1;
}

// constants
// these must remain 100 for the puzzle piece path stuff to work out
	const piecewidth = 100;
	const pieceheight = 100;

        // const gridRows = 2;
	const gridRows = 1; // Only one interactive row for now -JS
	const pipelineRow = 0;

	const gridOffset:fabric.Point = new fabric.Point(22,20);
	const canvasHeightInteractive = gridRows*pieceheight+gridOffset.y*2;

	// we should set canvas width appropriately
	let totalCanvasWidth = 1000;

    // Value for the 'accept' attribute for schema input (hardwired for now)
    const schemaAccept = ".json,.schema,.io,.ddl";

    // Value for the 'accept' attribute for non-csv data input (hardwired for now)
    const dataAccept = ".json,.input,.io,.data";

    // Error message for compile and execute tab when the source and target languages are not specified
    const sourceAndTargetRequired = "[ Both source and target languages must specified ]";

    // Error message for compile and execute (non-javascript) tab when the source and target languages are specified but the query src is not
    const noQuerySrc = "[ Query contents have not been specified ]";

    // Placeholder optimization when there are no optimizations chosen in a phase tab
    const optPlaceholder = "Add optimizations here";

// global variables
    // The web-worker that is actively running a query or null.  The kill button should only be visible when this is non-null.
    var worker:Worker = null;

    // The top-level tab manager (providing access to it from global functions)
    var tabManager:TabManager;

    // The main canvas (for late (re)-construction of tabs to be replaced in the top-level tab manager
    var mainCanvas:fabric.Canvas;

// Functions
    // A placeholder to fetch ancillary information not currently in Qcert.LanguageDescription
    // TODO integrate this
    function getSourceLanguageExtraInfo(source:Qcert.Language) : {accept: string, schemaForCompile: boolean} {
        switch (source) {
        case "sql":
            return {accept: ".sql", schemaForCompile: false};
        case "sqlpp":
            return {accept: ".sqlpp", schemaForCompile: false};
        case "oql":
            return {accept: ".oql", schemaForCompile: false};
        case "lambda_nra":
            return {accept: ".lnra", schemaForCompile: false};
        case "tech_rule":
            return {accept: ".arl", schemaForCompile: true};
        case "designer_rule":
            return {accept: ".sem", schemaForCompile: false};
        case "camp_rule":
            return {accept: ".rule,.camp", schemaForCompile: false};
        default:
            return undefined;
        }
    }

    // Executes when the kill button is pressed.  The kill button should only be visible when an execution is running, whether or not the execution tab is showing
    function killButton() {
        if (worker != null) {
            worker.terminate();
            worker = null;
            const executing = getExecOutputArea();
            if (executing != null)
                executing.value = "[ Execution interrupted ]";
            document.getElementById("kill-button").style.display = "none";
        }
    }

    // Executes when compile button is pressed.  This button shows when the compile tab shows.
    function compileButton() {
        const langs = getPipelineLangs();
        const optimconf = getOptimConfig();
        const srcInput = getSrcInput();
        const schemaInput = getSchemaInput();

        const theTextArea = <HTMLTextAreaElement>document.getElementById("compile-tab-query-output-text");

        const path = langs.map(x => x.id);
        if (path.length <= 2) {
            theTextArea.value = sourceAndTargetRequired;
            return;
        } else if (srcInput.length == 0) {
            theTextArea.value =  noQuerySrc;
            return;
        } else if (schemaInput.length == 0 || schemaInput == "{}") {
            if (getSourceLanguageExtraInfo(path[0]).schemaForCompile) {
                theTextArea.value = "[ The " + path[0] + " language requires a schema for compilation ]";
                return;
            }
        }
        theTextArea.value = "[ Compiling query ]";

        const middlePath = path.slice(1,-1);
        
        const handler = function(resultPack: Qcert.Result) {
            theTextArea.value = resultPack.result;
        }
        
        qcertWhiskDispatch({
            source:path[0],
            target:path[path.length-1],
            path:middlePath,
            exactpath:true,
            emitall:true,
            sourcesexp:false,
            ascii:false,
            javaimports:undefined,
            query:srcInput,
            schema: schemaInput,
            eval:false,
            input:undefined,
	    optims:JSON.stringify(optimconf) /* XXX Add optimizations here XXX */
          }, handler); 
    }

    // Executes when execute button is pressed.  This button shows when the execute tab shows.
    function executeButton() {
        const langs = getPipelineLangs();
        const optimconf = getOptimConfig();
        const path = langs.map(x => x.id);
	const executing = getExecOutputArea();

        if (worker != null) {
            executing.value = " [ A previous query is still executing and must be killed in order to execute a new one ]";
            return;
        }

        if (path.length <= 2) {
            executing.value = sourceAndTargetRequired;
            return;
        }

        const dataInput = getIOInput();
        if (dataInput.length == 0) {
            executing.value = "[ No input data specified ]";
            return;
        }
        
        executing.value = "[ Executing query ]";
        
        // expose the kill button
        document.getElementById("kill-button").style.display = "block";
        
        // Additional inputs
        const target = langs[langs.length-1].id;
        const schemaInput = getSchemaInput();
        
        // Setup to handle according to target language
        const arg:any = target == "js" ? setupJsEval(dataInput, schemaInput) : 
              setupQcertEval(path, getSrcInput(), schemaInput, dataInput, optimconf);
        if (arg == null) // error already detected and indicated
            return;

        // Processing is delegated to a web-worker
        try {
            // Worker variable is global (also executing and executingCanvas), making it (them) accessible to the killButton() function
            worker = new Worker("evalWorker.js");
            worker.onmessage = function(e) {
                workerComplete(e.data);
            }
            worker.onerror = function(e) {
                workerComplete(e.message);
            }
            console.log("About to post");
            console.log(arg);
            worker.postMessage(arg);
        } catch (err) {
            workerComplete(err.message);
        }
    }

    function setupJsEval(inputString:string, schemaText:string) : [string,string,string] {
        const compiledQuery = getCompiledQuery();
        if (compiledQuery == null) {
            const executing = getExecOutputArea();
            executing.value = "[ The query has not been compiled ]";
            return null;
        }
        return [inputString, schemaText, compiledQuery ];
    }
    
    function workerComplete(text:string) {
        const executing = getExecOutputArea();
        executing.value = text;
        document.getElementById("kill-button").style.display = "none";
        worker = null;
    }    

    function setupQcertEval(path:string[], srcInput:string, schemaInput:string, dataInput:string,optimconf:Qcert.OptimConfig[]) : Qcert.CompilerConfig {
        if (srcInput.length == 0) {
            const executing = getExecOutputArea();
            executing.value = noQuerySrc;
            return null;
        }
       const middlePath = path.slice(1,-1);
       return {source:path[0],
            target:path[path.length-1],
            path:middlePath,
            exactpath:true,
            emitall:true,
            sourcesexp:false,
            ascii:false,
            javaimports:undefined,
            query:srcInput,
            schema: schemaInput,
            eval: true,
            input: dataInput,
            optims:JSON.stringify(optimconf) /* XXX Add optimizations here XXX */
          };
    }

    // Executes when defaults button is pushed on the optim config tab
    function defaultConfig() {
        setConfig(Qcert.optimDefaults().optims);
        setConfigStatus("Default configuration was loaded.", false);
    }

    // Executes when clear button is pushed on the optim config tab
    function clearConfig() {
        setConfig(getClearConfig());
        setConfigStatus("Configuration starting from scratch", false);
    }

    // Executes when save button is pushed on the optim config tab
    function saveConfig() {
        const config = JSON.stringify(getOptimConfig());
        const blob = new Blob([config], {type: 'text/plain'});
        const url = URL.createObjectURL(blob);
        const link = document.createElement('a');
        link.href = url;
        link.download = "optimizations";
        link.click();
    }

    function getClearConfig() {
		function clearOptimsInOptimsList(optims:{[key: string]: string[];}) {
			for(const k in Object.keys(optims)) {
				optims[k] = [optPlaceholder];
			}
        }

        function clearOptimsInPhaseList(array:Qcert.OptimPhase[]) {
            array.forEach((elem) =>clearOptimsInOptimsList(elem.optims));
        }
        function clearOptimsInTopList(array:Qcert.OptimConfig[]) {
            array.forEach((elem) => clearOptimsInPhaseList(elem.phases));
            return array;
        }
        return clearOptimsInTopList(Qcert.optimDefaults().optims);
    }

    function setConfigStatus(text:string, usedFileChooser:boolean) {
        const msgarea = document.getElementById('config-message');
        msgarea.innerHTML = text;
        if (usedFileChooser)
            return;
        // Buttons that alter the config without going through the file chooser should clear file chooser state, which is no longer valid
        const chooser = document.getElementById('load-optims') as HTMLInputElement;
        chooser.value = "";
    }

    function setConfig(optims) {
        const newOptimsTab = OptimizationsTabMakeFromConfig(mainCanvas, optims);
        tabManager.replaceTab(newOptimsTab, 1);
        mainCanvas.renderAll();         
    }        

    function getSourceLeft(left:number):number {
		return left*(piecewidth + 30) + 20;
	}

	function getSourceTop(top:number):number {
		return canvasHeightInteractive + top*(pieceheight+30) + 20;
	}

	// The set of languages and their properties
	// const srcLanguageGroups:SourceLanguageGroups = {
	//     frontend:[{langid:'sql', label:'SQL'}, {langid:'oql', label:'OQL'}],
        //     intermediate:[{langid:'nrae', label:'NRAenv'}, {langid:'nrc', label:'NNRC'}],
        //     backend:[{langid:'js', label:'javascript'}, {langid:'cloudant', label:'Cloudant'}]};


	function toSrcLangDescript(color, sides:PuzzleSides) {
		return function(group:Qcert.LanguageDescription) {
		    return {langid:group.langid, label:group.label, langdescription:group.description, fill:color, sides:sides};
		}
	}
	
	function getSrcLangDescripts(langGroups:Qcert.SourceLanguageGroups) {
		let ret = [];
		ret.push(langGroups.frontend.map(toSrcLangDescript('#91D050', {right:-1})));
		ret.push(langGroups.core.map(toSrcLangDescript('#7AB0DD', {left: 1, right:-1})))
		ret.push(langGroups.distributed.map(toSrcLangDescript('#7AB0DD', {left: 1, right:-1})))
		ret.push(langGroups.backend.map(toSrcLangDescript('#ED7D32', {left: 1})));

		return ret;
	}

	// the boundary between the interactive and the selections
	let separatorLine = new fabric.Line([ 0, canvasHeightInteractive, totalCanvasWidth, canvasHeightInteractive], { stroke: '#ccc', selectable: false });

	function updateCanvasWidth(canvas:fabric.StaticCanvas, newWidth:number) {
		totalCanvasWidth = newWidth;
		canvas.setWidth(newWidth);
		separatorLine.set('x2', newWidth);
	}

	function ensureCanvasWidth(canvas:fabric.StaticCanvas, newWidth:number) {
		if(newWidth > totalCanvasWidth) {
			updateCanvasWidth(canvas, newWidth);
		}
	}

	function ensureCanvasInteractivePieceWidth(canvas:fabric.StaticCanvas, lastpiece:number) {
		ensureCanvasWidth(canvas, lastpiece*piecewidth);
	}

	function ensureCanvasSourcePieceWidth(canvas:fabric.StaticCanvas, lastpiece:number) {
		ensureCanvasWidth(canvas, getSourceLeft(lastpiece));
	}

	// Add support for hit testig individual objects in a group
 	// from http://stackoverflow.com/questions/15196603/using-containspoint-to-select-object-in-group#15210884
 	fabric.util.object.extend(fabric.Object.prototype, {
		getAbsoluteCenterPoint: function() {
		var point = this.getCenterPoint();
		if (!this.group)
			return point;
		var groupPoint = this.group.getAbsoluteCenterPoint();
		return {
			x: point.x + groupPoint.x,
			y: point.y + groupPoint.y
		};
		},
		containsInGroupPoint: function(point) {
		if (!this.group)
			return this.containsPoint(point);

		var center = this.getAbsoluteCenterPoint();
		var thisPos = {
			xStart: center.x - this.width/2,
			xEnd: center.x + this.width/2,
			yStart: center.y - this.height/2,
			yEnd: center.y + this.height/2
		}

		if (point.x >= thisPos.xStart && point.x <= (thisPos.xEnd)) {
			if (point.y >= thisPos.yStart && point.y <= thisPos.yEnd) {
				return true;
			}
		}
		return false;
	}});

// based on code from https://www.codeproject.com/articles/395453/html-jigsaw-puzzle
	function getMask(tileRatio, topTab, rightTab, bottomTab, leftTab) {

		var curvyCoords = [ 0, 0, 35, 15, 37, 5, 37, 5, 40, 0, 38, -5, 38, -5,
				20, -20, 50, -20, 50, -20, 80, -20, 62, -5, 62, -5, 60, 0, 63,
				5, 63, 5, 65, 15, 100, 0 ];
		const tileWidth = 100;
		const tileHeight = 100;
		var mask = "";
		var leftx = -4;
		var topy = 0;
		var rightx = leftx + tileWidth;
		var bottomy = topy + tileHeight;

		mask += "M" + leftx + "," + topy;

		//Top
		for (var i = 0; i < curvyCoords.length / 6; i++) {
			mask += "C";
			mask += leftx + curvyCoords[i * 6 + 0] * tileRatio;
			mask += ",";
			mask += topy + topTab * curvyCoords[i * 6 + 1] * tileRatio;
			mask += ",";
			mask += leftx + curvyCoords[i * 6 + 2] * tileRatio;
			mask += ",";
			mask += topy + topTab * curvyCoords[i * 6 + 3] * tileRatio;
			mask += ",";
			mask += leftx + curvyCoords[i * 6 + 4] * tileRatio;
			mask += ",";
			mask += topy + topTab * curvyCoords[i * 6 + 5] * tileRatio;
		}
		//Right
		for (var i = 0; i < curvyCoords.length / 6; i++) {
			mask += "C";
			mask += rightx - rightTab * curvyCoords[i * 6 + 1] * tileRatio;
			mask += ",";
			mask += topy + curvyCoords[i * 6 + 0] * tileRatio;
			mask += ",";
			mask += rightx - rightTab * curvyCoords[i * 6 + 3] * tileRatio;
			mask += ",";
			mask += topy + curvyCoords[i * 6 + 2] * tileRatio;
			mask += ",";
			mask += rightx - rightTab * curvyCoords[i * 6 + 5] * tileRatio;
			mask += ",";
			mask += topy + curvyCoords[i * 6 + 4] * tileRatio;
		}

		//Bottom
		for (var i = 0; i < curvyCoords.length / 6; i++) {
			mask += "C";
			mask += rightx - curvyCoords[i * 6 + 0] * tileRatio;
			mask += ",";
			mask += bottomy - bottomTab*curvyCoords[i * 6 + 1] * tileRatio;
			mask += ",";
			mask += rightx - curvyCoords[i * 6 + 2] * tileRatio;
			mask += ",";
			mask += bottomy - bottomTab * curvyCoords[i * 6 + 3] * tileRatio;
			mask += ",";
			mask += rightx - curvyCoords[i * 6 + 4] * tileRatio;
			mask += ",";
			mask += bottomy - bottomTab * curvyCoords[i * 6 + 5] * tileRatio;
		}

		
		//Left
		for (var i = 0; i < curvyCoords.length / 6; i++) {
			mask += "C";
			mask += leftx + leftTab * curvyCoords[i * 6 + 1] * tileRatio;
			mask += ",";
			mask += bottomy - curvyCoords[i * 6 + 0] * tileRatio;
			mask += ",";
			mask += leftx + leftTab * curvyCoords[i * 6 + 3] * tileRatio;
			mask += ",";
			mask += bottomy - curvyCoords[i * 6 + 2] * tileRatio;
			mask += ",";
			mask += leftx + leftTab * curvyCoords[i * 6 + 5] * tileRatio;
			mask += ",";
			mask += bottomy - curvyCoords[i * 6 + 4] * tileRatio;
		}

		return mask;
	}


function makeToolTip(
					tip:string,
					canvas:fabric.StaticCanvas,
					srcRect:{left:number, top:number, width:number, height:number},
					tooltipOffset:fabric.Point,
					textOptions:fabric.ITextOptions, 
					rectOptions:fabric.IRectOptions):fabric.Object {
	const topts = fabric.util.object.clone(textOptions);
	topts.left = 0;
	topts.top = 0;
	topts.editable = false;
	const text = new fabric.IText(tip, topts);
	// calculate where it should appear.

	// if needed, shrink the font so that the text
	// is not too large
	let boundingBox = text.getBoundingRect();
	const maxwidth = canvas.getWidth()*3/4;
	while(boundingBox.width > maxwidth) {
		text.setFontSize(text.getFontSize()-2);
		text.setCoords();
		boundingBox = text.getBoundingRect();
	}
	let piecemid = srcRect.left + Math.round(srcRect.width/2);

	let boxleft = piecemid - Math.round(boundingBox.width / 2);
	if(boxleft < 0) {
		boxleft = 0;
	} else {
		let tryright = piecemid + Math.round(boundingBox.width / 2);
		tryright = Math.min(tryright, canvas.getWidth());
		boxleft = tryright - boundingBox.width;
	}

	let boxtop = srcRect.top - boundingBox.height - tooltipOffset.y;
	if(boxtop < 0) {
		boxtop = srcRect.top + srcRect.height + tooltipOffset.y;
	}

	text.originX = 'left';
	text.left = boxleft;
	text.originY = 'top';
	text.top = boxtop;
	text.setCoords();
	const ropts = fabric.util.object.clone(rectOptions);
	fabric.util.object.extend(ropts, text.getBoundingRect());
	const box = new fabric.Rect(ropts);
	const group = new fabric.Group([box, text]);
	return group;
}

// interface IPuzzlePiece extends fabric.Object {
// 	// this should be in the fabric ts file
// 	canvas:fabric.StaticCanvas;

// 	// new stuff
// 	isSourcePiece?:boolean;
// 	isImplicit?:boolean;

// 	movePlace?:{left:number, top:number};
// 	langid:string;
// 	label:string;
// 	langdescription:string;
// 	tooltipObj?:fabric.Object;
// 	puzzleOffset:fabric.Point;
// 	getGridPoint:()=>fabric.Point;
// 	setGridPoint:(point:fabric.Point)=>void;
// 	setGridCoords:(x:number, y:number)=>void;

// 	// these are to help avoid accidentally setting
// 	// left or top without calling setCoords() after as required
// 	mySetLeft:(x:number)=>void;
// 	mySetTop:(y:number)=>void;
// 	mySetLeftAndTop:(x:number, y:number)=>void;
// 	readonly left:number;
// 	readonly top:number;
// }

// The class for a puzzle piece object


interface StringMap<V> {
	[K: string]: V;
}

// Either move sourcePieces inside the builder or move its initialization
// out to avoid maintenance/ordering problems

// These are two critical arrays for the buider
// This is the collection of source pieces
var sourcePieces:StringMap<SourcePuzzlePiece> = {};
// This is the matrix of pieces that are in the grid
var placedPieces:BasicPuzzlePiece[][] = [];
let errorPiece:SourcePuzzlePiece;

// things that can be get/set via the grid
interface Griddable {
	getGridPoint():fabric.Point;
	setGridPoint(point:fabric.Point):void;
	setGridCoords(x:number, y:number):void;
	isTransient():boolean;
}

interface Displayable {
	show();
	hide();
}

interface fabricObjectExt extends fabric.Object {
 		canvas:fabric.Canvas;
}

// function ext(obj:fabric.Object):fabricObjectExt {
// 	return <fabricObjectExt>obj;
// }

// objects that wrap a fabric object
interface FrontingObject {
	backingObject:fabricObjectExt;
	associate();
	deassociate();
}

function setBackingObject(f:FrontingObject, obj:fabric.Object) {
	f.backingObject = <fabricObjectExt>obj;
}

// function assignBackingObject(frontingObject:FrontingObject, backingObject:fabric.Object) {
// 	// disassociate the backingObject from any previous owner
// 	if(isBackingObject(backingObject)) {
// 		const oldObject = backingObject.frontingObject;
// 		oldObject.deassociate();
// 		delete oldObject.backingObject;
// 	}
// 	(<any>backingObject).frontingObject = frontingObject;
// 	frontingObject.backingObject = <BackingObject>(backingObject);
// 	frontingObject.associate();
// }

abstract class GriddablePuzzlePiece implements Griddable {
	
	getGridPoint():fabric.Point {
		return new fabric.Point(
			Math.round((this.backingObject.left + this.puzzleOffset.x - gridOffset.x) / piecewidth),
			Math.round((this.backingObject.top + this.puzzleOffset.y - gridOffset.y) / pieceheight));
	};

	setGridPoint(point:{x:number, y:number}):void {
		this.setGridCoords(point.x, point.y);
	};

	setGridCoords(x:number, y:number):void {
		this.backingObject.left = x * piecewidth - this.puzzleOffset.x + gridOffset.x;
		this.backingObject.top = y * pieceheight - this.puzzleOffset.y + gridOffset.y;
		this.backingObject.setCoords();
	};

	static calcPuzzleEdgeOffset(side:number):number {
		if(side < 0) {
			return 9;
		} else if(side > 0) {
			return 20;
		} else {
			return 0;
		}
	}

	abstract isTransient():boolean;
	backingObject:fabricObjectExt;
	puzzleOffset:fabric.Point;
}

class Grid {

	static remove(location:{x:number, y:number}) {
		let prow = placedPieces[location.y];
		if(prow === undefined) {
			return;
		}
		for(let i=location.x; i < prow.length; i++) {
			const p = i+1 < prow.length ? prow[i+1] : undefined;
			prow[i] = p;
			if(p !== undefined) {
				p.setGridCoords(i, location.y);
			}
		}
	}
        static removeAndHide(location:{x:number, y:number}) {
		let prow = placedPieces[location.y];
		if(prow === undefined) {
			return;
		}
		const p = prow[location.x];
		Grid.remove(location);
		if(p !== undefined) {
			p.hide();
		}
	}

	static addAndShow(location:{x:number, y:number}, pieces:BasicPuzzlePiece|BasicPuzzlePiece[]) {
		Grid.add(location, pieces);
		if(pieces instanceof Array) {
		    pieces.forEach(function(p:BasicPuzzlePiece) {p.show();});
		} else {
		    pieces.show();
		}
	}
/**
 * @param location The location where the first piece will be inserted
 * @param piece The piece(s) to be inserted.  The piece
 *        locations are not set. If this is desired, call {@link fixup locations} 
 * @returns the number of pieces that were moved out of the way
 */
	static add(location:{x:number, y:number}, pieces:BasicPuzzlePiece|BasicPuzzlePiece[]) {
		let prow = placedPieces[location.y];
		if(! (pieces instanceof Array)) {
			pieces = [pieces];
		}
		const numPieces = pieces.length;
		if(prow === undefined) {
			prow = [];
			placedPieces[location.y] = prow;
		} else {
			for(let i=prow.length-1; i >= location.x; i--) {
				const p = prow[i];
				const dest = i+numPieces;
				if(p !== undefined) {
					p.setGridCoords(dest, location.y);
				}
				prow[dest] = p;
			}
		}
		for(let i=0; i < numPieces; i++) {
			prow[location.x+i] = pieces[i];
		}
	}

	static fixupLocations(location:{x:number, y:number}, pieces:number) {
		const prow = placedPieces[location.y];
		if(prow === undefined) {
			return;
		}
		for(let i=0; i < pieces; i++) {
			const x = location.x+i;
			const p = prow[x];
			if(p !== undefined) {
				p.setGridCoords(x, location.y);
			}
		}
	}
}
	

class BasicPuzzlePiece extends GriddablePuzzlePiece implements FrontingObject, Displayable {

	langid:Qcert.Language;
	langdescription:string;
	previouslangid:Qcert.Language|null;
	previouslabel:string|null;

	isTransient() {
		return true;
	}

	readonly canvas:fabric.Canvas;
	options:any;
	backingObject:fabricObjectExt;	

	show() {
		this.canvas.add(this.backingObject);
	}

	hide() {
		this.canvas.remove(this.backingObject);
	}

        static make(canvas:fabric.Canvas, previouslangid:Qcert.Language, previouslabel:string, options):BasicPuzzlePiece {
	    const p = new BasicPuzzlePiece(canvas, previouslangid, previouslabel, {options:options});
	    p.associate();
	    return p;
	}

        protected constructor(canvas:fabric.Canvas, previouslangid:Qcert.Language, previouslabel:string, args:{options:any} | {srcpuzzle:BasicPuzzlePiece}) {
		super();
		this.canvas = canvas;

		if('options' in args) {
			let options = (<any>args).options;
			this.options = options;
			options || (options = { });
			options.width = piecewidth;
			options.height = pieceheight;
			const puzzleSides:PuzzleSides = options.sides || {};
			const puzzleLeft = puzzleSides.left || 0;
			const puzzleRight = puzzleSides.right || 0;
			const puzzleTop = puzzleSides.top || 0;
			const puzzleBottom = puzzleSides.bottom || 0;

			const puzzleOffsetPoint = new fabric.Point(GriddablePuzzlePiece.calcPuzzleEdgeOffset(puzzleLeft),
								GriddablePuzzlePiece.calcPuzzleEdgeOffset(puzzleTop));


			options.left = getSourceLeft(options.col || 0) - puzzleOffsetPoint.x;
			options.top = getSourceTop(options.row || 0) - puzzleOffsetPoint.y;
			options.hasControls = false;
			options.hasBorders = false;

			const path = new fabric.Path(getMask(1, puzzleTop, puzzleRight, puzzleBottom, puzzleLeft), options);

			// fix where the text appears
			const text = new fabric.Text(options.label, {
				fill: '#333',
				fontFamily: 'sans-serif',
				fontWeight: 'bold',
				fontSize: 15,
				left: options.left + 10 + (puzzleLeft > 0 ? 23 : 0),
				top: options.top + 10
			});
			// const bbox = text.getBoundingRect();

		        const group = new fabric.Group([path, text],
			{
				hasControls:false,
				hasBorders:false
			});
			setBackingObject(this, group);

			this.puzzleOffset = puzzleOffsetPoint;
		} else {
			// steal from another puzzle
			const src = (<any>args).srcpuzzle;
			this.options = src.options;
			this.backingObject = src.backingObject;
			this.puzzleOffset = src.puzzleOffset;
		}
	}

	deassociate() {
		
	};
	associate() {

	};

	// markSelected() {
	// 	console.log('selecting: ' + this.langid);
	// }

	// group.makeUnselected = function() {
	// 	console.log('deselecting: ' + this.langid);
	// }
}

class InteractivePuzzlePiece extends BasicPuzzlePiece {
	langid:Qcert.Language;
	label:string;
	langdescription:string;
	previouslangid:Qcert.Language|null;
	previouslabel:string|null;
	movePlace?:{left:number, top:number};

	isTransient() {
		return false;
	}

        static make(canvas:fabric.Canvas, previouslangid:Qcert.Language, previouslabel:string, src:BasicPuzzlePiece):InteractivePuzzlePiece {
	    const p = new InteractivePuzzlePiece(canvas, previouslangid, previouslabel, {srcpuzzle:src});
		p.associate();
		return p;
	}

        public constructor(canvas:fabric.Canvas, previouslangid:Qcert.Language, previouslabel:string, args:{options:any} | {srcpuzzle:BasicPuzzlePiece}) {
	    super(canvas, previouslangid, previouslabel, args);
		if('srcpuzzle' in args) {
			const options = (<any>args).srcpuzzle;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;
			this.previouslangid = previouslangid;
			this.previouslabel = previouslabel;
		} else {
			const options = (<any>args).options;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;
			this.previouslangid = previouslangid;
			this.previouslabel = previouslabel;
		}
	}

	associate() {
		this.backingObject.selectable  = true;
		this.backingObject.hoverCursor = 'grab';
		this.backingObject.moveCursor = 'grabbing';
		this.backingObject.on('mousedown', this.mousedown);
		this.backingObject.on('moving', this.moving); 
		this.backingObject.on('mouseup', this.mouseup); 
	}

	disassociate() {
		this.backingObject.off('mousedown', this.mousedown);
		this.backingObject.off('moving', this.moving); 
		this.backingObject.off('mouseup', this.mouseup); 
	}

	protected mousedown = () => {
		// Update source browser to point to the IL definition -JS
	        // Dealing with window focus is annoying, so disabled for now - JS
     	        if (this.previouslangid != null) {
   	            var illoc = makeTransitionURL(this.previouslangid,this.previouslabel,this.langid,this.label);
   	            var win = window.open(illoc, 'codebrowser');
   		    window.focus();
		}
		const gp = this.getGridPoint();
		this.backingObject.set({
			opacity:0.5
		});

		this.movePlace = {left:gp.x, top:gp.y};

	}

	protected mouseup = () => {
		this.backingObject.set({
			opacity:1
		});
		const gridp = this.getGridPoint();
		const leftentry = gridp.x;
		const topentry = gridp.y;

		this.setGridPoint(gridp);
	
		// fix this to use grid coordinates
		if(gridp.y < 0 || gridp.y >= gridRows) {
			Grid.remove(gridp);
			this.hide();
		}
		delete this.movePlace;

		// find the rightmost entry in the row
		const prow = placedPieces[topentry];
		if(prow !== undefined) {
			let maxcol:number;
			for(maxcol = prow.length-1; maxcol >= 0; maxcol--) {
				if(prow[maxcol] !== undefined) {
					break;
				}
			}
			ensureCanvasInteractivePieceWidth(this.canvas, maxcol+1);
		}


		// // update the placed grid
		// if('movePlace' in this) {
		// 	// finalize the moved pieces in their new positions
		// 	const prow = placedPieces[topentry];
		// 	if(! (prow === undefined)) {
		// 		let curleft = leftentry;
		// 		let curleftval = prow[leftentry];
		// 		while(! (curleftval === undefined)) {
		// 			let nextleft = curleft+1;
		// 			let nextleftval = prow[nextleft];

		// 			prow[nextleft] = curleftval;
		// 			curleft = nextleft;
		// 			curleftval = nextleftval;
		// 		}
		// 		ensureCanvasInteractivePieceWidth(this.canvas, curleft+1);
		// 		prow[leftentry] = undefined;
		// 	}
		// 	delete this['movePlace'];
		// }
		// if(topentry >= placedPieces.length || placedPieces[topentry] === undefined) {
		// 	placedPieces[topentry] = [];
		// }
		// const topplaces = placedPieces[topentry];
		// if(leftentry >= topplaces.length || topplaces[leftentry] === undefined) {
		// 	topplaces[leftentry] = this;
		// }

		// // finalize any left objects in their new positions
		// // remove any transient path objects
		// if('pathObjects' in this) {
		// 	for(let i =0; i < this.PathObjects.length; i++) {
		// 		const obj = this.PathObjects[i];
		// 		this.backingObject.canvas.remove(obj.backingObject);
		// 	}
		// 	delete this.PathObjects;			
		// }

	}
	
	protected moving = ():any => {
		const oldactualleft = this.backingObject.getLeft();
		const oldactualtop = this.backingObject.getTop();
		const gridp = this.getGridPoint();
		const originalleftentry = gridp.x;
		let leftentry = originalleftentry;
		const topentry = gridp.y;

		if('movePlace' in this) {
			if(this.movePlace.left == leftentry && this.movePlace.top == topentry) {
				// still over the same grid spot
				return;
			}

			const oldtop = this.movePlace.top;
			const oldleft = this.movePlace.left;
			const prow = placedPieces[oldtop];
			const shifted = InteractivePuzzlePiece.removeadjacentTransients({x:oldleft, y:oldtop});
			const newleft = oldleft - shifted;
			Grid.remove({x:newleft, y:oldtop});
			InteractivePuzzlePiece.addTransientsBefore({x:newleft, y:oldtop});
		}
			// // destroy any associated objects
			// if('pathObjects' in this) {
			// 	for(let i =0; i < this.PathObjects.length; i++) {
			// 		const obj = this.PathObjects[i];
			// 		this.backingObject.canvas.remove(obj.backingObject);
			// 	}
			// 	delete this.PathObjects;			
			// }
		// update, since it may have moved when we removed/added transients 
		leftentry = this.getGridPoint().x;
		this.backingObject.moveCursor = 'grabbing';
		const prow = placedPieces[topentry];
		let shifted:number = 0;

		if(prow !== undefined) {
			const existingPiece = prow[leftentry];
			if(existingPiece !== undefined) {
				if(existingPiece.isTransient()) {
					shifted = InteractivePuzzlePiece.removeadjacentTransients({x:leftentry, y:topentry});
					leftentry = leftentry - shifted;
					// also remove the current (transient) entry
					Grid.removeAndHide({x:leftentry, y:topentry});
					//leftentry = leftentry+1;
					Grid.add({x:leftentry, y:topentry}, this);
				} else {
					Grid.add({x:leftentry, y:topentry}, this);					
					shifted = InteractivePuzzlePiece.removeadjacentTransients({x:leftentry, y:topentry});
					leftentry = leftentry - shifted;
				}
			} else {
				Grid.add({x:leftentry, y:topentry}, this);									
			}
		} else {
			Grid.add({x:leftentry, y:topentry}, this);												
		}
		const movedBack:number = InteractivePuzzlePiece.addTransients({x:leftentry, y:topentry}, this);
		leftentry = leftentry + movedBack;
		if(leftentry == originalleftentry) {
			// if this is where we started, restore the (unsnapped) coordinates
			this.backingObject.setLeft(oldactualleft);
			this.backingObject.setTop(oldactualtop);
		} else {
			this.setGridCoords(leftentry, topentry);
		}
		this.canvas.renderAll();
		this.movePlace = {top:topentry, left:leftentry};
	}

	// TODO: would probably help to have a grid abstraction
	// which you add/move stuff with (instead of just setting/getting prow and stuff)
	// 

/**
 * Remove any transients (transient-transitively) next to point
 */
	static removeadjacentTransients(point:{x:number, y:number}):number {
		const cury = point.y;
		const prow = placedPieces[cury];
		if(prow === undefined) {
			return;
		}
		let curx = point.x+1;
		// delete stuff to the right
		while(true) {
			const p = prow[curx];
			if(p !== undefined && p.isTransient()) {
				Grid.removeAndHide({x:curx, y:cury});
			} else {
				break;
			}
		}
		// delete stuff to the left
		curx = point.x-1;
		while(curx >= 0) {
			const p = prow[curx];
			if(p !== undefined && p.isTransient()) {
				Grid.removeAndHide({x:curx, y:point.y});
				curx--;
			} else {
				break;
			}
		}
		return point.x-(curx+1);
	}


	static addTransientsBefore(afterpoint:{x:number, y:number}):number {
		const cury = afterpoint.y;
		const curx = afterpoint.x;
		const prow = placedPieces[cury];
		if(prow === undefined) {
			return 0;
		}

		const piece = prow[curx];
		if(piece === undefined) {
			return 0;
		}

		if(piece.isTransient()) {
			console.log("addTransientsBefore called next to a transient (right).  This should not happen.");
			return 0;
		}

		if(curx > 0) {
			const leftx = curx-1;
			const leftp = prow[leftx];
			if(leftp !== undefined) {
				if(leftp.isTransient()) {
					console.log("addTransientsBefore called next to a transient (left).  This should not happen.");
					return 0;
				}
				const leftpieces = InteractivePuzzlePiece.getPathTransients(<InteractivePuzzlePiece>leftp, <InteractivePuzzlePiece>piece);
				if(leftpieces.length > 0) {
					Grid.addAndShow(afterpoint, leftpieces);
					Grid.fixupLocations(afterpoint, leftpieces.length);
				}
				return leftpieces.length;
			} else {
				return 0;
			}
		} else {
			return 0;
		}
	}

	// add transients around a piece
	static addTransients(curpoint:{x:number, y:number}, piece:InteractivePuzzlePiece):number {
		const cury = curpoint.y;
		const curx = curpoint.x;
		const prow = placedPieces[cury];
		if(prow === undefined) {
			return 0;
		}
		const rightx = curx + 1;
		const rightp = prow[rightx];
		if(rightp !== undefined) {
			if(rightp.isTransient()) {
					console.log("addTransient called next to a transient (right).  This should not happen.");
					return 0;
				}
			const rightpieces = InteractivePuzzlePiece.getPathTransients(piece, <InteractivePuzzlePiece>rightp);
			if(rightpieces.length > 0) {
				Grid.addAndShow({y:cury, x:rightx}, rightpieces);
				// call fixup on them
				Grid.fixupLocations({y:cury, x:rightx}, rightpieces.length);
			}
		}

		if(curx > 0) {
			const leftx = curx-1;
			const leftp = prow[leftx];
			if(leftp !== undefined) {
				if(leftp.isTransient()) {
					console.log("addTransient called next to a transient (left).  This should not happen.");
					return 0;
				}
				const leftpieces = InteractivePuzzlePiece.getPathTransients(<InteractivePuzzlePiece>leftp, piece);
				if(leftpieces.length > 0) {
					Grid.addAndShow(curpoint, leftpieces);
					Grid.fixupLocations(curpoint, leftpieces.length);
				}
				return leftpieces.length;
			} else {
				return 0;
			}
		} else {
			return 0;
		}
	}

	// I need to figure out this whole interactive v transient thing better
	static getPathTransients(piece1:InteractivePuzzlePiece, piece2:InteractivePuzzlePiece):BasicPuzzlePiece[] {
		const curPath = Qcert.languagesPath({
			 			source: piece1.langid,
			 			target:piece2.langid
			 		}).path;
		const curPathLen = curPath.length;
		const transients:BasicPuzzlePiece[] = [];
		if(curPath == null 
				|| curPathLen == 0
				|| (curPathLen == 1 && curPath[0] == "error")) {
				// (<any>this.backingObject).moveCursor = 'no-drop';
				// add an error piece

		    transients.push(errorPiece.mkTransientDerivative(null,null));
		} else {
			for(let j = 1; j < curPathLen-1; j++) {
				const previouslangid = curPath[j-1];
				const langid = curPath[j];
			        const p = SourcePuzzlePiece.makeTransient(previouslangid,langid);
				// p.setGridCoords(leftentry+(j-1), topentry);
				// p.backingObject.top = p.backingObject.top + pieceheight/2;
				// p.backingObject.setCoords();
				transients.push(p);
				//this.backingObject.canvas.add(p.backingObject);
			}
		}
	        piece2.previouslangid = transients[transients.length-1].langid;
	        piece2.previouslabel = sourcePieces[transients[transients.length-1].langid].label;
		return transients;
	}
			// let nextentry = prow[leftentry];
			// if(nextentry === undefined) {
			// 	nextentry = prow[leftentry+1];
			// }
			// if(nextentry !== undefined) {
			// 	// ...
			// }
}

class SourcePuzzlePiece extends BasicPuzzlePiece {

	static makeBasic(langid:Qcert.Language):BasicPuzzlePiece {
		return sourcePieces[langid].mkBasicDerivative();
	}

        static makeTransient(prevlangid:Qcert.Language,langid:Qcert.Language):TransientPuzzlePiece {
	    var prevlabel = null;
	    if (prevlangid != null) {
		prevlabel = sourcePieces[prevlangid].label;
	    }
	    return sourcePieces[langid].mkTransientDerivative(prevlangid,prevlabel);
	}

	isTransient() {
		return true;
	}

	static make(canvas:fabric.Canvas, options):SourcePuzzlePiece {
		const p = new SourcePuzzlePiece(canvas, options);
		p.associate();
		return p;
	}

	langid:Qcert.Language;
	label:string;
	langdescription:string;

	protected constructor(canvas:fabric.Canvas, options) {
	    super(canvas, null, null, {options:options});	
	
		this.langid = options.langid;
		this.label = options.label;
		this.langdescription = options.langdescription;
	};

	associate() {
		this.backingObject.hoverCursor = 'grab';
		this.backingObject.moveCursor = 'grabbing';
		this.backingObject.on('mousedown', this.mousedown);
		this.backingObject.on('mouseover', this.mouseover); 
		this.backingObject.on('mouseout', this.mouseout); 
	};

	disassociate() {
		this.backingObject.off();
		// this.backingObject.off('mousedown', this.mousedown);
		// this.backingObject.off('mouseover', this.mouseover); 
		// this.backingObject.off('mouseout', this.mouseout); 
	}

	// TODO: when me move something, shift things to the right back over it (to the left)
	// be careful how that interacts with the shift right code!
	// TODO: work on getting things to move out of the way
	// track what we were over last / are over now
	// and use that to track what is going on
	// once that is working, change the code to move things over 
	// to use animations to look smooth

	// mkDerivative() {
	// 	// change to keep the same fronting object, with a new backingobject.
	// 	// which actually, can be automatically re-created upon disassociate
	// 	// instead, when dragging, we will create a new (BasicPuzzlePiece for now)
	// 	// and reassociate the backend with it

	// 	// new SourcePuzzlePiece(this.options);
	// // (<any>piece).mkDerivative = function () {
	// // 	var copyOfSelf = mkSourcePiece(options);
	// // 	copyOfSelf.isSourcePiece = false;
	// // 	return copyOfSelf;
	// }

	tooltipObj?:fabric.Object;

    protected mousedown = () => {
		// Update source browser to point to the IL definition -JS
		// Dealing with window focus is annoying, so disabled for now - JS
   	        var illoc = fixLabel(this.label)+".Lang."+fixLabel(this.label);
   	        var langURL = makeLemmaURL(illoc,this.langid);
   	        var win = window.open(langURL, 'codebrowser');
   		window.focus();
		// Rest of logic for moving puzzle pieces
		this.backingObject.set({
			opacity:.5
		});
		// clear any tooltip
		if('tooltipObj' in this) {
			this.backingObject.canvas.remove(this.tooltipObj);
			delete this.tooltipObj;
		}

		this.disassociate();
	        InteractivePuzzlePiece.make(this.canvas, null, null, this);
		// This could be optimized a bit
		// in particular, we can factor out the underlying puzzle piece,
		// and just create it and give it to the existing source piece
		// instead of creating a new source piece
		const newSourcePiece = SourcePuzzlePiece.make(this.canvas, this.options);
		this.backingObject.canvas.add(newSourcePiece.backingObject);
		sourcePieces[this.langid] = newSourcePiece;
		this.backingObject.canvas.renderAll();
	}

	mkBasicDerivative():BasicPuzzlePiece {
	    return BasicPuzzlePiece.make(this.canvas, null, null, this.options);
	}

        mkTransientDerivative(previouslangid:Qcert.Language, previouslabel:string):TransientPuzzlePiece {
	    return TransientPuzzlePiece.make(this.canvas, previouslangid, previouslabel, {options:this.options});
	}
	
	protected mouseover = () => {
		if(! ('tooltipObj' in this)) {
			const tip = makeToolTip(
				this.langdescription,
				this.backingObject.canvas,
				{left:this.backingObject.left, top:this.backingObject.top, width:piecewidth, height:pieceheight},
				new fabric.Point(10, 10),
				{fill:'black', fontSize:20}, 
				{fill:'#EEEEEE'});
			
			this.tooltipObj = tip;
			this.backingObject.canvas.add(tip);
		}
	};
	
	protected mouseout = () => {
		if('tooltipObj' in this) {
			this.backingObject.canvas.remove(this.tooltipObj);
			delete this.tooltipObj;
		}
	};
}

class TransientPuzzlePiece extends BasicPuzzlePiece {
	langid:Qcert.Language;
	label:string;
	langdescription:string;
	previouslangid:Qcert.Language|null;
	previouslabel:string|null;
	movePlace?:{left:number, top:number};
	movedPieces?:number;

	isTransient() {
		return true;
	}

        static make(canvas:fabric.Canvas, previouslangid:Qcert.Language,previouslabel:string,args:{options:any} | {srcpuzzle:BasicPuzzlePiece}):TransientPuzzlePiece {
	        const p = new TransientPuzzlePiece(canvas, previouslangid, previouslabel, args);
		p.associate();
		return p;
	}

	public constructor(canvas:fabric.Canvas, previouslangid:Qcert.Language,previouslabel:string,args:{options:any} | {srcpuzzle:BasicPuzzlePiece}) {
	        super(canvas, previouslangid, previouslabel, args);
		if('srcpuzzle' in args) {
			const options = (<any>args).srcpuzzle;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;
	                this.previouslangid = previouslangid;
	                this.previouslabel = previouslabel;
		} else {
			const options = (<any>args).options;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;
	                this.previouslangid = previouslangid;
	                this.previouslabel = previouslabel;
		}
	}

	protected mousedown = () => {
		// Update source browser to point to the IL definition -JS
		// Dealing with window focus is annoying, so disabled for now - JS
     	        if (this.previouslangid != null) {
   	            var illoc = makeTransitionURL(this.previouslangid,this.previouslabel,this.langid,this.label);
   	            var win = window.open(illoc, 'codebrowser');
   		    window.focus();
		}
	}

	protected mouseup = () => {
	}

	oldoptions?:{selectable:boolean, opacity:number};

	associate() {
		this.oldoptions = {
			selectable:this.backingObject.selectable,
			opacity:this.backingObject.getOpacity()
		};
		this.backingObject.selectable  = false;
		this.backingObject.setOpacity(0.25);
		this.backingObject.hoverCursor = 'pointer';
		this.backingObject.moveCursor = 'pointer';
		this.backingObject.on('mousedown', this.mousedown);
		//this.backingObject.on('moving', this.moving); 
		this.backingObject.on('mouseup', this.mouseup); 
	}

	disassociate() {
		if('oldoptions' in this) {
			this.backingObject.set(this.oldoptions);
			delete this.oldoptions;
		}
		this.backingObject.off('mousedown', this.mousedown);
		//this.backingObject.off('moving', this.moving); 
		this.backingObject.off('mouseup', this.mouseup); 
	}
}

// hm.  it would be really nice if we could make shorter pieces...
// a makeCompositePiece which takes in a list of puzzle pieces
// (which it can, of course, display as the hovertip.  Ideally it would take color from them too...)
// yay! the new getLRMask can do this!

// TODO: first get the implicit logic to work:
// when we need a new piece, create one piece (with first part of the chain?) and mark it implicit
// make sure all the logic works.
// after implicit pieces work, add support for composite pieces (which may also be implicit)

// TODO: create a makeCompositePiece that takes in a bunch of IPuzzlePieces
// and creates a single composite piece that can show the originals in a tooltip
// depending on which piece part you are actually hovering over, the tooltip will
// show that piece "bright"/selected and the others with a lower opacity

// separately, mark pieces as implicit if they are implicit
// If there is a single piece in a chain, it can be directly added (marked as implicit)
// if more, they are created, and then a composite (and implicit) chain will represent them.
// double clicking (if we can support that) on an implicit (either normal or composite)
// turns it into an explicit chain

// dropping on an implicit is allowed.  It does not make the implicit move out of the way,
// although it may generate a (possibly temporary) new implicit

// the logic will be a bit hairy :-)

// Of course, that piece will be marked as "generated"
// which means that 

// the sources that are passed in are owned (and manipulated directly) by the resulting composite object

class CompositePuzzlePiece extends GriddablePuzzlePiece implements Displayable, FrontingObject {
	static getLRMask(tileRatio, rightTab:number, leftTab:number, width:number) {

		var curvyCoords = [ 0, 0, 35, 15, 37, 5, 37, 5, 40, 0, 38, -5, 38, -5,
				20, -20, 50, -20, 50, -20, 80, -20, 62, -5, 62, -5, 60, 0, 63,
				5, 63, 5, 65, 15, 100, 0 ];
		const tileHeight = 100;
		var mask = "";
		var leftx = -4;
		var topy = 0;
		var rightx = leftx + width;
		var bottomy = topy + tileHeight;

		mask += "M" + leftx + "," + topy;
		mask += "L" + (leftx + width) + "," + topy;
		//Right
		for (var i = 0; i < curvyCoords.length / 6; i++) {
			mask += "C";
			mask += rightx - rightTab * curvyCoords[i * 6 + 1] * tileRatio;
			mask += ",";
			mask += topy + curvyCoords[i * 6 + 0] * tileRatio;
			mask += ",";
			mask += rightx - rightTab * curvyCoords[i * 6 + 3] * tileRatio;
			mask += ",";
			mask += topy + curvyCoords[i * 6 + 2] * tileRatio;
			mask += ",";
			mask += rightx - rightTab * curvyCoords[i * 6 + 5] * tileRatio;
			mask += ",";
			mask += topy + curvyCoords[i * 6 + 4] * tileRatio;
		}

		mask += "L" + leftx + "," + bottomy;
		
		//Left
		for (var i = 0; i < curvyCoords.length / 6; i++) {
			mask += "C";
			mask += leftx + leftTab * curvyCoords[i * 6 + 1] * tileRatio;
			mask += ",";
			mask += bottomy - curvyCoords[i * 6 + 0] * tileRatio;
			mask += ",";
			mask += leftx + leftTab * curvyCoords[i * 6 + 3] * tileRatio;
			mask += ",";
			mask += bottomy - curvyCoords[i * 6 + 2] * tileRatio;
			mask += ",";
			mask += leftx + leftTab * curvyCoords[i * 6 + 5] * tileRatio;
			mask += ",";
			mask += bottomy - curvyCoords[i * 6 + 4] * tileRatio;
		}

		return mask;
	}

	isTransient():boolean {
		return false;
	}

	static make(canvas:fabric.Canvas, gridx:number, gridy:number, sources:BasicPuzzlePiece[]) {
		const piece = new CompositePuzzlePiece(canvas, sources);
		piece.associate();
		piece.setGridCoords(gridx, gridy);
		return piece;
	}

	show() {
		this.canvas.add(this.backingObject);
	}

	hide() {
		this.canvas.remove(this.backingObject);
	}

	protected constructor(canvas:fabric.Canvas, sources:BasicPuzzlePiece[]) {
		super();

		this.puzzleOffset = new fabric.Point(GriddablePuzzlePiece.calcPuzzleEdgeOffset(1), 0);
		this.canvas = canvas;
		this.sources = sources;
		const sourceLen = sources.length;
		const pwidth = piecewidth / sourceLen;
		let parts:fabric.Object[] = [];
		let fulls:fabric.Object[] = [];
		for(let i=0; i < sourceLen; i++) {
			const p:BasicPuzzlePiece = sources[i];
			const ofull:fabric.Object = p.backingObject;
			const shortPiece = new fabric.Path(CompositePuzzlePiece.getLRMask(1, 1, -1, pwidth), {
				fill:p.backingObject.fill,
				opacity: 0.5,
				left:i*pwidth,
				top:0,
			});
			
			shortPiece.set({
				fill : '#6699ff',
				hasControls : false,
				selectable : false,
				evented : false,

			});
			ofull.setOpacity(p.backingObject.opacity/2);
			p.setGridCoords(i, 0);

			(<any>shortPiece).fullPiece = p;
			parts.push(shortPiece);
			fulls.push(ofull);
		}
		this.fullGroup = new fabric.Group(fulls);

		setBackingObject(this, new fabric.Group(parts));
		this.parts = parts;
		this.lastSelectedPart = -1;
	}

	readonly canvas:fabric.Canvas;
	readonly fullGroup:fabric.Object;
	readonly parts:fabric.Object[];
	readonly sources:BasicPuzzlePiece[];

	tooltipObj?:fabric.Object;
	lastSelectedPart:number;

	updateTooltip() {

		// abstract the logic from makeToolTip?
		// fix where it appears!
		const tipbound = this.fullGroup.getBoundingRect();
		const compositebound = this.backingObject.getBoundingRect();

		
		this.fullGroup.setLeft(compositebound.left + (compositebound.width - tipbound.width) / 2);
		this.fullGroup.setTop(compositebound.top + compositebound.height + 10);
		const tip = this.fullGroup;

		if(! ('tooltipObj' in this)) {
			this.tooltipObj = tip;
			this.canvas.add(tip);
		}
	};

	findSubTarget(e:Event, lastIndex:number):number {
		const mousePos = this.canvas.getPointer(e);
		const mousePoint = new fabric.Point(mousePos.x, mousePos.y);

		if(lastIndex >= 0) {
			const part:any = this.parts[lastIndex];
			if(part.containsInGroupPoint(mousePoint)) {
				return lastIndex;
			}
		}
		for(let i=0; i < this.parts.length; i++) {
			if(i == lastIndex) {
				continue;
			}

			const part:any = this.parts[i];
			if(part.containsInGroupPoint(mousePoint)) {
				return i;
			}
		}
		return -1;
	}

	
	updateTooltipFocus(e:Event) {
		const newSelectedPart = this.findSubTarget(e, this.lastSelectedPart);
		if(this.lastSelectedPart == newSelectedPart) {
			return;
		}
		if(this.lastSelectedPart >= 0) {
			const lastpartpiece:any = this.parts[this.lastSelectedPart];
			//lastpart.makeUnselected();
		}
		if(newSelectedPart >= 0) {
			const newpart:any = this.sources[newSelectedPart];
			//newpart.makeSelected();
		}
		this.lastSelectedPart = newSelectedPart;
		this.canvas.renderAll();
	}

	deleteTooltip() {
		if('tooltipObj' in this) {
			this.canvas.remove(this.tooltipObj);
			delete this.tooltipObj;
		}
	}

	mousemovehandler = (e:fabric.IEvent) => {
		if(e.target == this.backingObject) {
			if(! ('tooltipObj' in this)) {
				this.updateTooltip();
			} 
			this.updateTooltipFocus(e.e);
		}
	}

	mouseover = () => {
		this.canvas.on('mouse:move', this.mousemovehandler);
	}

	mouseout = () => {
		this.canvas.off('mouse:move', this.mousemovehandler);
		this.deleteTooltip();
	}

	moving = () => {
		this.updateTooltip();
	}

	associate() {
		this.backingObject.on('mouseover', this.mouseover);
		this.backingObject.on('mouseout', this.mouseout);
		this.backingObject.on('moving', this.moving);
	}

	deassociate() {
		this.backingObject.off('mouseover', this.mouseover);
		this.backingObject.off('mouseout', this.mouseout);
		this.backingObject.off('moving', this.moving);
	}
}

function getLangPiece(langid:string):BasicPuzzlePiece {
	return SourcePuzzlePiece.makeBasic(langid);
}

const defaultTabTextOpts:fabric.ITextOptions = { 
	fontFamily: 'sans-serif',
};

const defaultTabRectOpts:fabric.IRectOptions = {
	cornerSize:2,
	strokeLineCap:'round'
}

abstract class CanvasTab {
	constructor(canvas:fabric.Canvas) {
		this.canvas = canvas;
	}
	abstract getLabel():string;
	getRectOptions():fabric.IRectOptions {
		return defaultTabRectOpts;
	}
	getTextOptions():fabric.ITextOptions {
		return defaultTabTextOpts;
	}
	abstract show():void;
	hide() {
		this.canvas.clear();
	}
	canvas:fabric.Canvas;
	canvasObj?:fabric.Object;
}

abstract class CanvasDynamicTab extends CanvasTab {
		constructor(canvas:fabric.Canvas) {
			super(canvas);
	}
	/**
	 * returns true if the name change is successfull
	 */
	abstract setLabel(newlabel:string):boolean;
}

type TabManagerOptions = {label:string, 
					rectOptions?:fabric.IRectOptions, 
					textOptions?:fabric.IITextOptions, 
					tabOrigin?:{left?:number, top?:number},
					};

class TabManager extends CanvasTab {
	static makeTab(tab:CanvasTab, top:number, left:number):fabric.Object {
       const ropts = fabric.util.object.clone(defaultTabRectOpts);
	   fabric.util.object.extend(ropts, tab.getRectOptions() || {});

       ropts.left = left;
       ropts.top = top;
       ropts.editable = false;
       ropts.height = ropts.height || 30;
       ropts.width = ropts.width || 150;
       const box = new fabric.Rect(ropts);


	   const topts = fabric.util.object.clone(defaultTabTextOpts)
	   fabric.util.object.extend(topts, tab.getTextOptions() || {});
       topts.left = 0;
       topts.top = 0;
       topts.editable = false;
	   const text = new fabric.IText(tab.getLabel(), topts);
       // calculate where it should appear.

       // if needed, shrink the font so that the text
       // is not too large
       let boundingBox = text.getBoundingRect();
       const maxwidth = ropts.width - 4;
       while(boundingBox.width > maxwidth) {
               text.setFontSize(text.getFontSize()-2);

               text.setCoords();
               boundingBox = text.getBoundingRect();
       }

	   
       text.originX = 'left';
       text.left = ropts.left + (ropts.width -  boundingBox.width) / 2;
       text.originY = 'top';
       text.top = ropts.top;
       text.height = ropts.height;
       text.width = ropts.width;
       text.setTextAlign('center');
       text.setCoords();
       const group = new fabric.Group([box, text]);
	   group.hasControls = false;
	   group.hasBorders = false;
	   group.lockMovementX = true;
	   group.lockMovementY = true;
	   tab.canvasObj = group;
	   group.setOpacity(0.3);
       return group;
	}
					
	static make(canvas:fabric.Canvas, 
				options:TabManagerOptions, 
				tabs:CanvasTab[], startTab:number=-1):TabManager {
        console.log("Making tab manager with label " + options.label + " and initial tab " + startTab + " and " + tabs.length + " tabs");
		const tm = new TabManager(canvas, options, tabs);
		tm.setInitTab(tabs, startTab);
		return tm;
	}

	protected setInitTab(tabs:CanvasTab[], startTab:number) {
		if(startTab >= 0 && startTab < tabs.length) {
			const t = tabs[startTab];
			if(t !== undefined && t !== null) {
				this.currentTab = t;
				if('canvasObj' in t) {
					const tabobj = t.canvasObj;
					tabobj.setOpacity(1);
				}
			}
		}

	}
	protected constructor(canvas:fabric.Canvas, 
					options:TabManagerOptions, 
					tabs:CanvasTab[]) {
		super(canvas);
		this.label = options.label;
		this.rectOpts = options.rectOptions || defaultTabRectOpts;
		this.textOpts = options.textOptions || defaultTabTextOpts;
		this.tabObjects = [];

		const defaultTabOrigin = {left:10, top:5};

		const tabOrigin = options.tabOrigin || defaultTabOrigin;
		const tabTop = tabOrigin.top || defaultTabOrigin.top;
       	let tabLeft = tabOrigin.left || defaultTabOrigin.left;
		

       for(let i=0; i < tabs.length; i++) {
			const itab = tabs[i];
			const tabgroup = TabManager.makeTab(itab, tabTop, tabLeft);
			tabLeft += tabgroup.getBoundingRect().width;
			tabgroup.hoverCursor = 'pointer';
			tabgroup.on('selected', () => {
				this.switchTab(itab);
			});

			this.tabObjects.push(tabgroup);
       }
	}
    
    replaceTab(newTab:CanvasTab, position:number) {
        const oldGroup = this.tabObjects[position];
        const rect = oldGroup.getBoundingRect();
        console.log("Old tab:");
        console.log(this.currentTab);
        const newGroup = TabManager.makeTab(newTab, rect.top, rect.left);
        newGroup.hoverCursor = 'pointer';
        newGroup.on('selected', () => {
            this.switchTab(newTab);
        });
        this.tabObjects.forEach((obj) => this.canvas.remove(obj));
        this.tabObjects[position] = newGroup;
        this.tabObjects.forEach((obj) => this.canvas.add(obj));
        if (oldGroup === this.currentTab.canvasObj) {
            this.switchTab(newTab);
        }
        console.log("New tab:");
        console.log(newTab);
        this.canvas.renderAll();
    }    

	readonly label:string;
	readonly rectOpts:fabric.IRectOptions;
	readonly textOpts:fabric.IITextOptions;
	tabObjects:fabric.Object[];

	getLabel():string {
		return this.label;
	}

	getRectOptions():fabric.IRectOptions {
		return this.rectOpts;
	}
	getTextOptions():fabric.ITextOptions {
		return this.textOpts;
	}
	show():void {
		if(this.currentTab != null) {
			this.currentTab.show();
		}
		this.tabObjects.forEach((obj) => this.canvas.add(obj));
	}
	hide() {
		if(this.currentTab != null) {
			this.currentTab.hide();
		}
		this.tabObjects.forEach((obj) => this.canvas.remove(obj));
	}

	currentTab:CanvasTab = null;

	switchTab(tab:CanvasTab) {
		if(this.currentTab != null) {
			if('canvasObj' in this.currentTab) {
				const tabobj = this.currentTab.canvasObj;
				tabobj.setOpacity(0.3);
			}
			this.currentTab.hide();
		}
		this.currentTab = tab;
		tab.show();
		if('canvasObj' in tab) {
			const tabobj = tab.canvasObj;
			tabobj.setOpacity(1);
		}
	}
}

class BuilderTab extends CanvasTab {

	static make(canvas:fabric.Canvas) {
		return new BuilderTab(canvas);
	}

	startPiece:BasicPuzzlePiece;
	totalCanvasHeight:number;
	maxCols:number;

	constructor(canvas:fabric.Canvas) {
		super(canvas);
		separatorLine.set('visible', true);

	        const startPiece = BasicPuzzlePiece.make(canvas, null, null, {
			fill : '#bfe49a',
			label : 'start',
			sides : {right:-1},
			hasControls : false,
			selectable : false,
			evented : false
		});
		startPiece.setGridCoords(0, pipelineRow);
		startPiece.backingObject.set({
			hasControls : false,
			selectable: false
		});
		startPiece.backingObject.hoverCursor = 'auto';

		this.startPiece = startPiece;

		const runText = new fabric.Text('R\nu\nn', {
			left:2,
			fontSize:25,
			top:pipelineRow * pieceheight + gridOffset.y + 1,
			textAlign:'center',
			width:20,
			fill:'red',
			height:pieceheight
		});

		const runRect = new fabric.Rect({
			left:0,
			top:pipelineRow * pieceheight + gridOffset.y,
			width:20,
			height:pieceheight-2,
			stroke:'red',
			strokeWidth:2
		});
		const runGroup:any = new fabric.Group([runRect, runText]);
		runGroup.set({
			hasControls:false,
			selectable:false
		});

		runGroup.on('mouseover', function() {
			if(! ('tooltipObj' in runGroup)) {
				// TODO: add path information here (at least for now)
				const tip = makeToolTip(
					"Run the compiler!",
					canvas,
					{left:runGroup.left, top:runGroup.top, width:20, height:pieceheight},
					new fabric.Point(10, 10),
					{fill:'black', fontSize:40}, 
					{fill:'#EEEEEE'});
				
					runGroup.tooltipObj = tip;
					runGroup.canvas.add(tip);
				}
		});
		runGroup.on('mouseout', function() {
			if('tooltipObj' in runGroup) {
				canvas.remove(runGroup.tooltipObj);
				delete runGroup.tooltipObj;
			}
		});

		const srcLangDescripts = getSrcLangDescripts(Qcert.languages());
		let maxCols:number = 0;
		// create the list of languages that can be dragged onto the canvas
		let srcrow=0;
		for(srcrow=0; srcrow < srcLangDescripts.length; srcrow++) {
			let rowelem = srcLangDescripts[srcrow];
			if(rowelem == null) {
				continue;
			}
			let srccol=0;
			for(srccol=0; srccol < rowelem.length; srccol++) {
				let colelem = rowelem[srccol];
				if(colelem == null) {
					continue;
				}

				colelem.row = srcrow;
				colelem.col = srccol;
				let piece = SourcePuzzlePiece.make(canvas, colelem);
				sourcePieces[colelem.langid] = piece;
			}
			maxCols = Math.max(srccol, maxCols);
		}

		const errorOptions = {
			langid:'error', 
			label:'Error', 
			langdescription:'This represents an error, probably an unsupported path',
			fill:'#ff3300', sides:{}
		};

		errorPiece = SourcePuzzlePiece.make(canvas, errorOptions);

		const canvasHeightChooser = srcrow;
		this.maxCols = maxCols;
		this.totalCanvasHeight = getSourceTop(srcrow)-15;

		//const canvasElement = document.getElementById('main-canvas');
	}

	getLabel():string {
		return "Path Builder ";
	}

	getRectOptions() {
		return {fill:'#FEBF01'};
	}

	show():void {
		// TODO: at some point enable this
		// but upon creation remove any inappropriate (source) elements
		// and set up the mouse up/down/hover code
		// taking care that the algorithm may now need to move things multiple spaces

		// canvas.on('selection:created', function (event) {
		// 	canvas.getActiveGroup().set({hasControls : false});
		// });

		// canvas.on('object:moving', function (event) {
		// 	const piece = event.target;
		// 	piece.set({
		// 	left: Math.round(piece.left / piecewidth) * piecewidth,
		// 	top: Math.round(piece.top / pieceheight) * pieceheight
		// 	});
		// });
		
		// disable group selection
		//canvas.selection = false;

		// create the start piece
		// note that the start piece is meant to have a "real" piece put on top of it by the user
		const canvas = this.canvas;
		canvas.selection = false;
		canvas.hoverCursor = 'pointer';

		this.startPiece.show();

		//canvas.add(runGroup);
		canvas.add(separatorLine);

		// add the source pieces
		for(let piece in sourcePieces) {
			sourcePieces[piece].show();
		}

		// add the grid pieces
		const placedRows = placedPieces.length;
		for(let row=0;row < placedRows; row++) {
			const prow = placedPieces[row];
			if(prow !== undefined) {
				const placedCols = prow.length;
				for(let col=0;col < placedCols; col++) {
					const piece = prow[col];
					if (piece !== undefined) {
						piece.show();
					}
				}
			}
		}
		// make sure the canvas is wide enough
		ensureCanvasSourcePieceWidth(canvas, this.maxCols);
		// TODO: also make sure that it is wide enough for the pieces in the grid
		canvas.setHeight(this.totalCanvasHeight);

		// TODO experimental
		// const g = CompositePuzzlePiece.make(canvas, 1, 1, 
		// 	[getLangPiece("nraenv"),
		// 	getLangPiece("nra"), 
		// 	getLangPiece("camp")]);
		// g.show();
		// TODO end:experimental
		canvas.renderAll();
	}
}

class CompileTab extends CanvasTab {
	titleTextElement:Node;
	inputTabElement:HTMLElement;
	queryInput:HTMLElement;
	defaultTitleTextElement:Node;
    queryChooser:HTMLInputElement;
    schemaChooser:HTMLInputElement;

	static make(canvas:fabric.Canvas) {
		return new CompileTab(canvas);
	}

	constructor(canvas:fabric.Canvas) {
	    super(canvas);
	    this.inputTabElement = document.getElementById("compile-tab");
	    this.titleTextElement = document.getElementById("compile-tab-lang-title");
	    this.defaultTitleTextElement = <HTMLElement>this.titleTextElement.cloneNode(true);
	    this.queryInput = document.getElementById("compile-tab-query-input");
            this.queryChooser = <HTMLInputElement>document.getElementById("compile-tab-query-src-file");
            this.schemaChooser = <HTMLInputElement>document.getElementById("compile-tab-query-schema-file"); 
	}

	getLabel() {
		return "Compilation ";
	}
	
	getRectOptions() {
		return {fill:'#FEBF01'};
	}

	static getSrcLanguagePiece() {
		const pipeline = getPipelinePieces();
		if(pipeline === undefined || pipeline.length == 0) {
			return errorPiece;
		} else {
			return pipeline[0];
		}
	}

	clearTitle() {
		while(this.titleTextElement.hasChildNodes()) {
			this.titleTextElement.removeChild(this.titleTextElement.firstChild);
		}
	}

	setErrorTitleText() {
		const newNode = this.defaultTitleTextElement.cloneNode(true)
		this.titleTextElement.parentNode.replaceChild(newNode, this.titleTextElement);
		this.titleTextElement = newNode;
	}

	setSrcLanguage(piece:BasicPuzzlePiece) {
	    this.clearTitle();
	    const titleElem = document.createElement('label');
	    titleElem.appendChild(document.createTextNode("Input Language: " + piece.langid + " [" + piece.langdescription + "]"));
	    this.titleTextElement.appendChild(titleElem);
            const langInfo = getSourceLanguageExtraInfo(piece.langid);
            this.queryChooser.accept = langInfo.accept;
            // the following is static for now but set here since it may become dynamic in the future
            this.schemaChooser.accept = schemaAccept;
	}

	update() {
	    const srcpiece = CompileTab.getSrcLanguagePiece();
	    if(srcpiece.langid == 'error') {
		this.setErrorTitleText();
		this.queryInput.style.display="none";
	    } else {
		this.setSrcLanguage(srcpiece);
		this.queryInput.style.display="block";
	    }
	}

	show() {
		this.clearTitle();
		this.update();

		this.inputTabElement.style.display="block";
		this.canvas.getElement().style.display="none";

	}

	hide() {
		this.canvas.getElement().style.display="block";
		this.inputTabElement.style.display="none";
	}
}

class ExecTab extends CanvasTab {
    titleTextElement:Node;
    inputTabElement:HTMLElement;
    dataInput:HTMLElement;
    defaultTitleTextElement:Node;
    dataChooser:HTMLInputElement;

    static make(canvas:fabric.Canvas) {
        return new ExecTab(canvas);
    }

    constructor(canvas:fabric.Canvas) {
        super(canvas);
        this.inputTabElement = document.getElementById("execute-tab");
        this.titleTextElement = document.getElementById("execute-tab-lang-title");
        this.defaultTitleTextElement = <HTMLElement>this.titleTextElement.cloneNode(true);
        this.dataInput = document.getElementById("execute-tab-query-input");
        this.dataChooser = <HTMLInputElement>document.getElementById("execute-tab-query-io-file");
    }

    getLabel() {
        return " Evaluation ";
    }
    
    getRectOptions() {
        return {fill:'#FEBF01'};
    }

    static getSrcLanguagePiece() {
        const pipeline = getPipelinePieces();
        if(pipeline === undefined || pipeline.length == 0) {
            return errorPiece;
        } else {
            return pipeline[0];
        }
    }

    clearTitle() {
        while(this.titleTextElement.hasChildNodes()) {
            this.titleTextElement.removeChild(this.titleTextElement.firstChild);
        }
    }

    setErrorTitleText() {
        const newNode = this.defaultTitleTextElement.cloneNode(true)
        this.titleTextElement.parentNode.replaceChild(newNode, this.titleTextElement);
        this.titleTextElement = newNode;
    }

    setSrcLanguage(piece:BasicPuzzlePiece) {
        this.clearTitle();
        const titleElem = document.createElement('label');
        titleElem.appendChild(document.createTextNode("Input Language: " + piece.langid + " [" + piece.langdescription + "]"));
        this.titleTextElement.appendChild(titleElem);
        // the following is static for now but set here since it may become dynamic in the future
        this.dataChooser.accept = dataAccept;
    }

    update() {
        const srcpiece = CompileTab.getSrcLanguagePiece();
        if(srcpiece.langid == 'error') {
            this.setErrorTitleText();
            this.dataInput.style.display="none";
        } else {
            this.setSrcLanguage(srcpiece);
            this.dataInput.style.display="block";
        }
    }

    show() {
        this.clearTitle();
        this.update();

        this.inputTabElement.style.display="block";
        this.canvas.getElement().style.display="none";

    }

    hide() {
        this.canvas.getElement().style.display="block";
        this.inputTabElement.style.display="none";
    }
}

function getPipelinePieces():BasicPuzzlePiece[] {
	const prow = placedPieces[pipelineRow];
	const path:BasicPuzzlePiece[] = [];
	if(prow === undefined) {
		return path;
	}
	const rowLen = prow.length;
	for(let col = 0; col < rowLen; col++) {
		const piece = prow[col];
		if(piece === undefined) {
			return path;
		}
		path.push(piece);
	}
	return path;
}

function getPipelineLangs():{id:Qcert.Language,explicit:boolean}[] {
	return getPipelinePieces().map(function (piece) {
		if('langid' in piece) {
			return {id:(<any>piece).langid, explicit:! piece.isTransient()};
		} else {
			return undefined;
		}
	});
}

// function expandLangsPath(path:Qcert.Language[]):{id:Qcert.Language,explicit:boolean}[] {
// 	let expanded = [];
// 	const pathLen = path.length;
// 	if(path == null || pathLen == 0) {
// 		return expanded;
// 	}

// 	let prev = path[0];
// 	expanded.push({id:prev, explicit:true});
// 	for(let i = 1; i < pathLen; i++) {
// 		const cur = path[i];
// 		const curPath = Qcert.LanguagesPath({
// 			source: prev,
// 			target:cur
// 		}).Path;
// 		const curPathLen = curPath.length;

// 		if(curPath == null 
// 		|| curPathLen == 0
// 		|| (curPathLen == 1 && curPath[0] == "error")) {
// 			expanded.push("error");
// 		} else {
// 			for(let j = 1; j < curPathLen; j++) {
// 				expanded.push({id:curPath[j], explicit:(j+1)==curPathLen});
// 			}
// 		}
// 		prev = cur;
// 	}

// 	return expanded;
// }

function getLanguageMarkedLabel(langpack:{id:Qcert.Language, explicit:boolean}):string {
	const lang = langpack.id;
	let str:string = "";
	if(lang in sourcePieces) {
		str = sourcePieces[lang].label;
	} else {
		str = "error";
	}

	if(! langpack.explicit) {
		str = "[" + str + "]";
	}
	return str;
}

//const coqdocBaseURL = 'https://querycert.github.io/doc/';
//const coqdocBaseURL = '../..//querycert.github.io/doc/';
const coqdocBaseURL = '../html/';
function makeLemmaURL(base:string, lemma:string) {
	let url = coqdocBaseURL + "Qcert." + base + ".html";
	//let url = coqdocBaseURL + base + ".html";
	if(lemma != undefined) {
		url = url + "#" + lemma;
	}
	return url;
}
function fixLabel(label) {
    if (label == "SQL++") return "SQLPP";
    if (label == "NRAᵉ") return "NRAEnv";
    if (label == "cNRAᵉ") return "cNRAEnv";
    if (label == "λNRA") return "LambdaNRA";
    return label;
}
function makeTransitionURL(previouslangid, previouslabel, langid, label) {
    var label = fixLabel(label);
    var previouslabel = fixLabel(previouslabel);
    if (previouslangid == langid) {
	return makeLemmaURL(label+".Optim."+label+"Optimizer","run_"+langid + "_optims");
	//return makeLemmaURL(label+"Optimizer","run_"+langid + "_optims");
    }
    else {
	return makeLemmaURL("Translation."+previouslabel+"to"+label,previouslangid + "_to_" + langid + "_top");
	//return makeLemmaURL(previouslabel+"to"+label,previouslangid + "_to_" + langid + "_top");
    }
}
function makeOptimElement(modulebase:string, o:Qcert.OptimStepDescription):HTMLLIElement {
	const entry = document.createElement('li');
	entry.classList.add("optim-list");
	entry.appendChild(document.createTextNode(o.name));
	const lemmaLink = document.createElement('a');
	lemmaLink.href = makeLemmaURL(modulebase, o.lemma);
	lemmaLink.appendChild(document.createTextNode('✿'));
	lemmaLink.classList.add('lemma-link');
        lemmaLink.setAttribute('target','codebrowser');
	entry.appendChild(lemmaLink);
	entry.title = o.description;
	entry.setAttribute('data-id', o.name);
	return entry;
}

function makeAvailableOptimElement(modulebase:string, o:Qcert.OptimStepDescription):HTMLLIElement {
	return makeOptimElement(modulebase, o);
}

function addRemoveButton(elem:HTMLElement) {
    if (elem.innerText === optPlaceholder)
        return;
	const removenode = document.createElement('i');
	removenode.classList.add('js-remove');
	removenode.appendChild(document.createTextNode('✖'));
	elem.appendChild(removenode);
}

function makeSimpleOptimElement(optim:string) {
	const entry = document.createElement('li');
	entry.classList.add('optim-list');

	entry.appendChild(document.createTextNode(optim));
    entry.setAttribute('data-id', optim);
	return entry;
}

function makePhaseOptimElement(
	modulebase:string,
	optims:Qcert.OptimStepDescription[],
	optim:string):HTMLLIElement {

	const fulloptim = findFirstWithField(optims, 'name', optim);
	const entry = fulloptim ? makeOptimElement(modulebase, fulloptim) : makeSimpleOptimElement(optim);
	addRemoveButton(entry);
	return entry;
}

function getCountWithUpdate(listnode:HTMLElement) {
    const count = listnode.childElementCount;
    if (count == 1 && listnode.children.item(0).innerHTML == optPlaceholder)
        return 0;
    if (count == 0) {
        listnode.appendChild(makeSimpleOptimElement(optPlaceholder));
        return 0;
    }
    if (count > 1)
        for (let i = 0; i < count; i++) {
            if (listnode.children.item(i).innerHTML == optPlaceholder) {
                listnode.removeChild(listnode.children.item(i));
                return count - 1;
            }
    }
    return count;
}

class OptimPhaseTab extends CanvasDynamicTab {
	static make(canvas:fabric.Canvas,
		parentDiv:HTMLElement, 
		modulebase:string,
		optims:Qcert.OptimStepDescription[],

		phase:Qcert.OptimPhase, 
		options:{color:string, top?:number}):OptimPhaseTab {
		return new OptimPhaseTab(canvas, parentDiv, modulebase, optims, phase, "top", options);
	}

	constructor(canvas:fabric.Canvas,
		div:HTMLElement,  
		modulebase:string,
		optims:Qcert.OptimStepDescription[],

		phase:Qcert.OptimPhase,
		optimsType:string,
		options:{color:string, top?:number}) {
		
		super(canvas);
		this.name = phase.name;
		this.iter = phase.iter;
		this.top = options.top || 0;
		this.color = options.color || '#FEBF01';

		//this.body = document.getElementsByTagName("body")[0];
		this.parentDiv = div;
		const newdiv = document.createElement('div');
		this.optimDiv = newdiv;
		this.optimsType = optimsType;


		const divTitle = document.createElement('h3');
		divTitle.style.cssFloat = 'center';
		const titlenodetext = (num:number) => "Currently selected optimizations (" + num + ")";
        let displayedCount = phase.optims[optimsType].length;
        if (displayedCount == 0)
            phase.optims[optimsType] = [ optPlaceholder ];
        else if (displayedCount == 1 && phase.optims[optimsType][0] == optPlaceholder)
            displayedCount = 0;
		const titlenode = document.createTextNode(titlenodetext(displayedCount));
		divTitle.appendChild(titlenode);
		newdiv.appendChild(divTitle);
		const divIterations = document.createElement('h4');
		divIterations.appendChild(document.createTextNode("These optimizations will be batched in " + phase.iter + " iterations "));
		newdiv.appendChild(divIterations);

		const listnode = document.createElement('ul');
		listnode.classList.add('optim-list');

		for(let i =0 ; i < phase.optims[optimsType].length; i++) {
			listnode.appendChild(makePhaseOptimElement(modulebase, optims, phase.optims[optimsType][i]));
		}

		function updateListAndTitleContent() {
            const elemCount = getCountWithUpdate(listnode);
			titlenode.textContent = titlenodetext(elemCount);
		}

		const sort = Sortable.create(listnode, 
		{
			group: {
				name: 'optims',
				pull: true,
				put: true
			},
			sort: true,
			animation: 150,
			//handle: '.optim-handle',
			filter: '.js-remove',
  			onFilter: function (evt) {
    			var el = sort.closest(evt.item); // get dragged item
    			el && el.parentNode.removeChild(el);
				updateListAndTitleContent();
  			},
			onAdd: function (evt) {
				const item = evt.item;
				addRemoveButton(item);
			},
			onSort: function(evt) {
				updateListAndTitleContent();
			},
			dataIdAttr: 'data-id'
		}
		);
		this.sortable = sort;

		newdiv.appendChild(listnode);
	}
	
	readonly sortable:Sortable;
	readonly top:number;
	readonly color:string;
	name:string;
	iter:number;

	getPhase():Qcert.OptimPhase {
        let optims:string[] = this.sortable.toArray();
        console.log(optims);
        if (optims.length == 1 && optims[0] == optPlaceholder)
            optims = [];
		const ret = {
			name:this.name,
			optims:{},
			iter: this.iter
		};
		ret.optims[this.optimsType] = optims;
		return ret;
	}

	getLabel():string {
		return this.name;
	}

	setLabel(newlabel:string):boolean {
		this.name = newlabel;
		return true;
	}
	
	getRectOptions() {
		return {fill:this.color};
	}

	parentDiv:HTMLElement;
	optimDiv:HTMLElement;

	optimsType:string;
	show() {
		this.parentDiv.appendChild(this.optimDiv);		

		//this.canvas.add(this.rect);
	}

	hide() {
		this.parentDiv.removeChild(this.optimDiv);
		//this.canvas.remove(this.rect);
	}
}

function optimPhaseMake(canvas:fabric.Canvas, 	
	div:HTMLElement,
	module_base:string,
	optims:Qcert.OptimStepDescription[],
options:{color:string, top?:number}) {
	return function(phase:Qcert.OptimPhase) {
		return OptimPhaseTab.make(canvas, div, module_base, optims, phase, options);
	}

}

class OptimizationManager extends CanvasTab {
	
	static make(canvas:fabric.Canvas, 
				options:{rectOptions?:fabric.IRectOptions, textOptions?:fabric.IITextOptions, tabOrigin?:{left?:number, top?:number}}, 
				language:Qcert.Language,
				modulebase:string,
				optims:Qcert.OptimStepDescription[],
				cfg_phases:Qcert.OptimPhase[],
				startTab:number=-1):OptimizationManager {
					
		const tm = new OptimizationManager(canvas, options, language, modulebase, optims, cfg_phases);
		return tm;
	}

	language:Qcert.Language;
	optimTabs:OptimPhaseTab[];
	tabManager:TabManager;
	parentDiv:HTMLElement;
	topDiv:HTMLElement;
	phasesDiv:HTMLElement;

	rectOptions?:fabric.IRectOptions;
	textOptions?:fabric.IITextOptions;

	protected constructor(
		canvas:fabric.Canvas, 
		options:{rectOptions?:fabric.IRectOptions, textOptions?:fabric.IITextOptions, tabOrigin?:{left?:number, top?:number}}, 
		language:Qcert.Language,
		module_base:string,
		optims:Qcert.OptimStepDescription[],
		cfg_phases:Qcert.OptimPhase[]) {

		super(canvas);
		this.language = language;
		this.rectOptions = options.rectOptions;
		this.textOptions = options.textOptions;
		const defaultTabOrigin = {left:10, top:5};

		const tabOrigin = options.tabOrigin || defaultTabOrigin;
		const tabTop = tabOrigin.top || defaultTabOrigin.top;
       	const tabLeft = tabOrigin.left || defaultTabOrigin.left;
		
		this.parentDiv = document.getElementById("container");
		const newdiv = document.createElement('div');
		newdiv.style.position='absolute';
		newdiv.style.left='10px';
		newdiv.style.top=String(tabTop+60) + 'px';
		this.topDiv = newdiv;
		const listnode = document.createElement('ul');

		listnode.classList.add('optim-list');
		for(let i =0 ; i < optims.length; i++) {
			const o = optims[i];
			const entry = makeAvailableOptimElement(module_base, o);

			listnode.appendChild(entry);
		}

		const leftdiv = document.createElement('div');
		leftdiv.classList.add('phase-optims');
		leftdiv.style.position = 'static';
		leftdiv.style.cssFloat = 'left';

		const rightdiv = document.createElement('div');
		rightdiv.classList.add('all-optims');
		rightdiv.style.position = 'static';
		rightdiv.style.cssFloat = 'right';
		rightdiv.style.paddingLeft='40px';
		const rightDivTitle = document.createElement('h3');
		rightDivTitle.style.cssFloat = 'center';
		rightDivTitle.appendChild(document.createTextNode("Available optimizations (" + optims.length + ")"));
		rightdiv.appendChild(rightDivTitle);
		rightdiv.appendChild(listnode);

		const sort = Sortable.create(listnode, 
		{
			group: {
				name: 'optims',
				pull: 'clone',
				put: false
			},
			sort: false,
			animation: 150
		}
		);


		newdiv.appendChild(leftdiv);
		newdiv.appendChild(rightdiv);		


		this.phasesDiv = leftdiv;

		const yoffset2 = tabTop+60;
	
		this.optimTabs = cfg_phases.map(optimPhaseMake(canvas, leftdiv, module_base, optims, {color:'#ED7D32', top:yoffset2}));

		this.tabManager = TabManager.make(canvas, 
				{
					label:language,
					rectOptions:options.rectOptions,
			 		textOptions:options.textOptions, 
				 	tabOrigin:options.tabOrigin
				}, this.optimTabs, 0);
		

	}

	getOptimConfig():Qcert.OptimConfig {
		return {
			language:this.language,
			phases:this.getConfigPhases()
		}
	}
	
	getConfigPhases():Qcert.OptimPhase[] {
		return this.optimTabs.map((x) => x.getPhase());
	}

	getLabel():string {
		return this.language;
	}

	getRectOptions():fabric.IRectOptions {
		return this.rectOptions;
	}

	getTextOptions():fabric.ITextOptions {
		return this.textOptions;
	}

	show() {
		this.tabManager.show();
		this.parentDiv.appendChild(this.topDiv);
        document.getElementById('optim-config-buttons').style.display = "block";		
	}

	hide() {
		this.tabManager.hide();
		this.parentDiv.removeChild(this.topDiv);		
        document.getElementById('optim-config-buttons').style.display = "none";      
	}
}

function findFirstWithField<T, K extends keyof T>(l:T[], field:K, lang:T[K]):T {
	const f = l.filter((x) => x[field] == lang);
	if(f.length == 0) {
		return undefined;
	} else {
		return f[0];
	}
}

// TODO: turn this into a wrapper class so that 
// globalOptimTabs, OptimizationsTabMake, and getOptimConfig
// are encapsulated
let globalOptimTabs:OptimizationManager[];

function OptimizationsTabMake(canvas:fabric.Canvas) {
    return OptimizationsTabMakeFromConfig(canvas, Qcert.optimDefaults().optims);
}

function OptimizationsTabMakeFromConfig(canvas:fabric.Canvas, defaults:Qcert.OptimConfig[]) {
	const yoffset = 60;
    const optims = Qcert.optimList().optims;

    console.log("Setting optimization config");
    console.log(optims);
    
	const opts = {rectOptions:{fill:'#548235'}, tabOrigin:{top:yoffset}};	
	let optimTabs:OptimizationManager[] = [];
	for(let i=0; i < optims.length; i++) {
		const opt = optims[i];
		const cfg = findFirstWithField(defaults, 'language', opt.language.name);
		const cfg_phases = cfg === undefined ? [] : cfg.phases;

		optimTabs.push(OptimizationManager.make(canvas, opts, opt.language.name, opt.language.modulebase, opt.optims["top"], cfg_phases));
	}
	globalOptimTabs = optimTabs;
	return TabManager.make(canvas, {label:"Optim Config", rectOptions:{fill:'#FEBF01'}}, optimTabs, 0);
}

function getOptimConfig():Qcert.OptimConfig[] {
	if(globalOptimTabs) {
		return globalOptimTabs.map((x) => x.getOptimConfig());
	} else {
		return [];
	}
}

const tabinitlist:((canvas:fabric.Canvas)=>CanvasTab)[] = [
    BuilderTab.make,
    OptimizationsTabMake,
    CompileTab.make,
    ExecTab.make
];

function init():void {
	mainCanvas = new fabric.Canvas('main-canvas');
	const tabscanvas = new fabric.Canvas('tabs-canvas');

	const tabs = tabinitlist.map(function (elem) {
		return elem(mainCanvas)
	});
	const tm = TabManager.make(tabscanvas, {label:"Q*cert"}, tabs, 0);
	tm.show();
	tabscanvas.renderAll();
    tabManager = tm;
}

function handleCSVs(files:FileList) {
    console.log("CSV file handler called");
    var readFiles = {};
    function readFile(index) {
        if (index >= files.length) {
            completeCSVs(readFiles);
            return;
        }
        var file = files[index];
        var reader = new FileReader();  
        reader.onload = function(event) {
            var typeName = (<any>file.name).endsWith(".csv") ? file.name.substring(0, file.name.length - 4) : file.name;
            readFiles[typeName] = (<any>event.target).result;
            readFile(index+1);
        }
        reader.readAsText(file);
    }
    readFile(0);
}

function completeCSVs(readFiles) {
    let schemaText = (<HTMLTextAreaElement>document.getElementById("compile-tab-query-schema-text")).value;
    if (schemaText.length == 0) {
        getExecInputArea().value = "[ Error: A schema must be specified (on the compile tab) to parse CSV files ]";
        let form = <HTMLFormElement>document.getElementById('csvs-form');
        form.reset();
        return;
    }
    let delimiter = (<HTMLTextAreaElement>document.getElementById("delimiter")).value;
		getExecInputArea().value = JSON.stringify({delimiter: delimiter, data: readFiles});
}

function handleOptimFile(files:FileList) {
    if (files.length > 0) {
        const file = files[0];
        const reader = new FileReader();
        reader.onload = function(event) {
            const contents:string = (<any>event.target).result;
            const optims = JSON.parse(contents) as Qcert.OptimConfig[];
            addEmptyPhases(optims);
            setConfig(optims);
            setConfigStatus("Configuration loaded from " + file.name, true);
        } 
        reader.readAsText(file);
    }
}

function addEmptyPhases(optims:Qcert.OptimConfig[]) {
    const empty = getClearConfig();
    for (let i = 0; i < empty.length; i++) {
        const conf = empty[i];
        const match = findFirstWithField(optims, 'language', conf.language);
        if (match) {
            const emptyPhases = conf.phases;
            const matchPhases = match.phases;
            for (let j = 0; j < emptyPhases.length; j++) {
                const phase = emptyPhases[j];
                const phaseMatch = findFirstWithField(matchPhases, 'name', phase.name);
                if (!phaseMatch)
                    // Add the empty phase
                    matchPhases.push(phase);
            }
        } else
            // Add the entire empty language with all its phases
            optims.push(conf);
    }
}

function handleFile(output:string, isSchema:boolean, files:FileList) {
    if (files.length > 0) {
        const file = files[0];
        const reader = new FileReader();
        const outputElem:HTMLTextAreaElement = <HTMLTextAreaElement>document.getElementById(output);
        outputElem.value = "[ Reading ]";
        if ((<any>file.name).endsWith(".sem")) {
            reader.onload = function(event) {
                const contents:string = btoa(String.fromCharCode.apply(null,
                        new Uint8Array((<any>event.target).result)))
                outputElem.value = contents;
            }
            reader.readAsArrayBuffer(file);
        } else {
            reader.onload = function(event) {
                const contents:string = (<any>event.target).result;
                outputElem.value = contents;
            }
            reader.readAsText(file);
        }
    }
}

function handleFileDrop(output:string, event:DragEvent) {
	event.stopPropagation();
  	event.preventDefault();
	var dt = event.dataTransfer;
  	var files = dt.files;
	handleFile(output, false, files);
}

function getSrcInput():string {
	const elem = <HTMLTextAreaElement>document.getElementById('compile-tab-query-src-text');
	return elem.value;
}

function getSchemaInput():string {
    const elem = <HTMLTextAreaElement>document.getElementById('compile-tab-query-schema-text');
    return elem.value.length > 0 ? elem.value : "{}";
}

function getIOInput():string {
	return getExecInputArea().value;
}

function getExecOutputArea():HTMLTextAreaElement {
    return <HTMLTextAreaElement>document.getElementById('execute-tab-query-output-text');
}

function getExecInputArea():HTMLTextAreaElement {
    return <HTMLTextAreaElement>document.getElementById('execute-tab-query-io-text');
}

function getCompiledQuery():string {
    const elem = <HTMLTextAreaElement>document.getElementById('compile-tab-query-output-text');
    return elem.value;
}
