
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

	const gridRows = 2;
	const pipelineRow = 0;

	const gridOffset:fabric.IPoint = new fabric.Point(22,20);
	const canvasHeightInteractive = gridRows*pieceheight+gridOffset.y*2;

	// we should set canvas width appropriately
	let totalCanvasWidth = 1000;

// global variables
    var compiledQuery:string = null;
    var worker:Worker = null;
    var executing:any = null;
    var executingCanvas:any = null;

// Functions
    function killButton() {
        if (worker != null) {
            worker.terminate();
            worker = null;
            if (executing != null && executingCanvas != null) {
                ensureFit(executingCanvas, executing, "[ Execution terminated ]");
            }
        }
    }

    function ensureFit(canvas:fabric.ICanvas, text:fabric.IText, newText:string) {
        text.setText(newText);
        canvas.setHeight(text.getHeight());
        canvas.setWidth(text.getWidth());
        canvas.renderAll();
    }

    function getSourceLeft(left:number):number {
		return left*(piecewidth + 30) + 20;
	}

	function getSourceTop(top:number):number {
		return canvasHeightInteractive + top*(pieceheight+30) + 20;
	}

	// The set of languages and their properties
	// const srcLanguageGroups:SourceLanguageGroups = {
	// 	frontend:[{langid:'sql', label:'SQL'}, {langid:'oql', label:'OQL'}],
    //     intermediate:[{langid:'nrae', label:'NRAenv'}, {langid:'nrc', label:'NNRC'}],
    //     backend:[{langid:'js', label:'javascript'}, {langid:'cloudant', label:'Cloudant'}]};


	function toSrcLangDescript(color, sides:PuzzleSides) {
		return function(group:QcertLanguageDescription) {
			return {langid:group.langid, label:group.label, langdescription:group.description, fill:color, sides:sides};
		}
	}
	
	function getSrcLangDescripts(langGroups:SourceLanguageGroups) {
		let ret = [];
		ret.push(langGroups.frontend.map(toSrcLangDescript('#33cc33', {right:-1})));
		ret.push(langGroups.intermediate.map(toSrcLangDescript('#6699ff', {left: 1, right:-1})))
		ret.push(langGroups.backend.map(toSrcLangDescript('#ff3300', {left: 1})));

		return ret;
	}

	// the boundary between the interactive and the selections
	let separatorLine = new fabric.Line([ 0, canvasHeightInteractive, totalCanvasWidth, canvasHeightInteractive], { stroke: '#ccc', selectable: false });

	function updateCanvasWidth(canvas:fabric.IStaticCanvas, newWidth:number) {
		totalCanvasWidth = newWidth;
		canvas.setWidth(newWidth);
		separatorLine.set('x2', newWidth);
	}

	function ensureCanvasWidth(canvas:fabric.IStaticCanvas, newWidth:number) {
		if(newWidth > totalCanvasWidth) {
			updateCanvasWidth(canvas, newWidth);
		}
	}

	function ensureCanvasInteractivePieceWidth(canvas:fabric.IStaticCanvas, lastpiece:number) {
		ensureCanvasWidth(canvas, lastpiece*piecewidth);
	}

	function ensureCanvasSourcePieceWidth(canvas:fabric.IStaticCanvas, lastpiece:number) {
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
					canvas:fabric.IStaticCanvas,
					srcRect:{left:number, top:number, width:number, height:number},
					tooltipOffset:fabric.IPoint,
					textOptions:fabric.ITextOptions, 
					rectOptions:fabric.IRectOptions):fabric.IObject {
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

// interface IPuzzlePiece extends fabric.IObject {
// 	// this should be in the fabric ts file
// 	canvas:fabric.IStaticCanvas;

// 	// new stuff
// 	isSourcePiece?:boolean;
// 	isImplicit?:boolean;

// 	movePlace?:{left:number, top:number};
// 	langid:string;
// 	label:string;
// 	langdescription:string;
// 	tooltipObj?:fabric.IObject;
// 	puzzleOffset:fabric.IPoint;
// 	getGridPoint:()=>fabric.IPoint;
// 	setGridPoint:(point:fabric.IPoint)=>void;
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
	getGridPoint():fabric.IPoint;
	setGridPoint(point:fabric.IPoint):void;
	setGridCoords(x:number, y:number):void;
	isTransient():boolean;
}

interface Displayable {
	show();
	hide();
}

// objects that are wrapped by customization
declare module fabric {
	export interface IObject  {
		canvas:ICanvas;
		moveCursor:string;
	}
}

// objects that wrap a fabric object
interface FrontingObject {
	backingObject:fabric.IObject;
	associate();
	deassociate();
}

// function assignBackingObject(frontingObject:FrontingObject, backingObject:fabric.IObject) {
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
	
	getGridPoint():fabric.IPoint {
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
	backingObject:fabric.IObject;
	puzzleOffset:fabric.IPoint;
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

	langid:QcertLanguage;
	langdescription:string;

	isTransient() {
		return true;
	}

	readonly canvas:fabric.ICanvas;
	options:any;
	backingObject:fabric.IObject;

	show() {
		this.canvas.add(this.backingObject);
	}

	hide() {
		this.canvas.remove(this.backingObject);
	}

	static make(canvas:fabric.ICanvas, options):BasicPuzzlePiece {
		const p = new BasicPuzzlePiece(canvas, {options:options});
		p.associate();
		return p;
	}

	protected constructor(canvas:fabric.ICanvas, args:{options:any} | {srcpuzzle:BasicPuzzlePiece}) {
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
				fontWeight: 'bold',
				fontSize: 20,
				left: options.left + 10 + (puzzleLeft > 0 ? 23 : 0),
				top: options.top + 10
			});
			// const bbox = text.getBoundingRect();

			const group = new fabric.Group([path, text],
			{
				hasControls:false,
				hasBorders:false
			});
			this.backingObject = group;

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
	langid:QcertLanguage;
	label:string;
	langdescription:string;
	movePlace?:{left:number, top:number};

	isTransient() {
		return false;
	}

	static make(canvas:fabric.ICanvas, src:BasicPuzzlePiece):InteractivePuzzlePiece {
		const p = new InteractivePuzzlePiece(canvas, {srcpuzzle:src});
		p.associate();
		return p;
	}

	public constructor(canvas:fabric.ICanvas, args:{options:any} | {srcpuzzle:BasicPuzzlePiece}) {
		super(canvas, args);
		if('srcpuzzle' in args) {
			const options = (<any>args).srcpuzzle;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;
		} else {
			const options = (<any>args).options;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;

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
		// 	for(let i =0; i < this.pathObjects.length; i++) {
		// 		const obj = this.pathObjects[i];
		// 		this.backingObject.canvas.remove(obj.backingObject);
		// 	}
		// 	delete this.pathObjects;			
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
			// 	for(let i =0; i < this.pathObjects.length; i++) {
			// 		const obj = this.pathObjects[i];
			// 		this.backingObject.canvas.remove(obj.backingObject);
			// 	}
			// 	delete this.pathObjects;			
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
		const curPath = qcertLanguagesPath({
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

			transients.push(errorPiece.mkTransientDerivative());
		} else {
			for(let j = 1; j < curPathLen-1; j++) {
				const langid = curPath[j];
				const p = SourcePuzzlePiece.makeTransient(langid);
				// p.setGridCoords(leftentry+(j-1), topentry);
				// p.backingObject.top = p.backingObject.top + pieceheight/2;
				// p.backingObject.setCoords();
				transients.push(p);
				//this.backingObject.canvas.add(p.backingObject);
			}
		}
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

	static makeBasic(langid:QcertLanguage):BasicPuzzlePiece {
		return sourcePieces[langid].mkBasicDerivative();
	}

	static makeTransient(langid:QcertLanguage):TransientPuzzlePiece {
		return sourcePieces[langid].mkTransientDerivative();
	}

	isTransient() {
		return true;
	}

	static make(canvas:fabric.ICanvas, options):SourcePuzzlePiece {
		const p = new SourcePuzzlePiece(canvas, options);
		p.associate();
		return p;
	}

	langid:QcertLanguage;
	label:string;
	langdescription:string;

	protected constructor(canvas:fabric.ICanvas, options) {
		super(canvas, {options:options});	
	
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
		// this.backingObject.off('mousdown', this.mousedown);
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

	tooltipObj?:fabric.IObject;

	protected mousedown = () => {
		this.backingObject.set({
			opacity:.5
		});
		// clear any tooltip
		if('tooltipObj' in this) {
			this.backingObject.canvas.remove(this.tooltipObj);
			delete this.tooltipObj;
		}

		this.disassociate();
		InteractivePuzzlePiece.make(this.canvas, this);
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
		return BasicPuzzlePiece.make(this.canvas, this.options);
	}

	mkTransientDerivative():TransientPuzzlePiece {
		return TransientPuzzlePiece.make(this.canvas, {options:this.options});
	}
	
	protected mouseover = () => {
		if(! ('tooltipObj' in this)) {
			const tip = makeToolTip(
				this.langdescription,
				this.backingObject.canvas,
				{left:this.backingObject.left, top:this.backingObject.top, width:piecewidth, height:pieceheight},
				new fabric.Point(10, 10),
				{fill:'black', fontSize:40}, 
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
	langid:QcertLanguage;
	label:string;
	langdescription:string;
	movePlace?:{left:number, top:number};
	movedPieces?:number;

	isTransient() {
		return true;
	}

	static make(canvas:fabric.ICanvas, args:{options:any} | {srcpuzzle:BasicPuzzlePiece}):TransientPuzzlePiece {
		const p = new TransientPuzzlePiece(canvas, args);
		p.associate();
		return p;
	}

	public constructor(canvas:fabric.ICanvas, args:{options:any} | {srcpuzzle:BasicPuzzlePiece}) {
		super(canvas, args);
		if('srcpuzzle' in args) {
			const options = (<any>args).srcpuzzle;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;
		} else {
			const options = (<any>args).options;
			this.langid = options.langid;
			this.label = options.label;
			this.langdescription = options.langdescription;

		}
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
		//this.backingObject.on('mousedown', this.mousedown);
		//this.backingObject.on('moving', this.moving); 
		//this.backingObject.on('mouseup', this.mouseup); 
	}

	disassociate() {
		if('oldoptions' in this) {
			this.backingObject.set(this.oldoptions);
			delete this.oldoptions;
		}
		//this.backingObject.off('mousedown', this.mousedown);
		//this.backingObject.off('moving', this.moving); 
		//this.backingObject.off('mouseup', this.mouseup); 
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

	static make(canvas:fabric.ICanvas, gridx:number, gridy:number, sources:BasicPuzzlePiece[]) {
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

	protected constructor(canvas:fabric.ICanvas, sources:BasicPuzzlePiece[]) {
		super();

		this.puzzleOffset = new fabric.Point(GriddablePuzzlePiece.calcPuzzleEdgeOffset(1), 0);
		this.canvas = canvas;
		this.sources = sources;
		const sourceLen = sources.length;
		const pwidth = piecewidth / sourceLen;
		let parts:fabric.IObject[] = [];
		let fulls:fabric.IObject[] = [];
		for(let i=0; i < sourceLen; i++) {
			const p:BasicPuzzlePiece = sources[i];
			const ofull:fabric.IObject = p.backingObject;
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

		this.backingObject = new fabric.Group(parts);
		this.parts = parts;
		this.lastSelectedPart = -1;
	}

	readonly canvas:fabric.ICanvas;
	readonly fullGroup:fabric.IGroup;
	readonly parts:fabric.IObject[];
	readonly sources:BasicPuzzlePiece[];

	tooltipObj?:fabric.IObject;
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
	fontFamily: 'Impact',
  	stroke: '#c3bfbf',
  	strokeWidth: 1
};

const defaultTabRectOpts:fabric.IRectOptions = {
	cornerSize:2,
	strokeLineCap:'round'
}

abstract class ICanvasTab {
	constructor(canvas:fabric.ICanvas) {
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
	canvas:fabric.ICanvas;
	canvasObj?:fabric.IObject;
}

abstract class ICanvasDynamicTab extends ICanvasTab {
		constructor(canvas:fabric.ICanvas) {
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

class TabManager extends ICanvasTab {
	static makeTab(canvas:fabric.IStaticCanvas, tab:ICanvasTab, top:number, left:number):fabric.IObject {
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
					
	static make(canvas:fabric.ICanvas, 
				options:TabManagerOptions, 
				tabs:ICanvasTab[], startTab:number=-1):TabManager {
		const tm = new TabManager(canvas, options, tabs);
		tm.setInitTab(tabs, startTab);
		return tm;
	}

	protected setInitTab(tabs:ICanvasTab[], startTab:number) {
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
	protected constructor(canvas:fabric.ICanvas, 
					options:TabManagerOptions, 
					tabs:ICanvasTab[]) {
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
			const tabgroup = TabManager.makeTab(canvas, itab, tabTop, tabLeft);
			tabLeft += tabgroup.getBoundingRect().width;
			tabgroup.hoverCursor = 'pointer';
			tabgroup.on('selected', () => {
				this.switchTab(itab);
			});

			this.tabObjects.push(tabgroup);
       }
	}

	readonly label:string;
	readonly rectOpts:fabric.IRectOptions;
	readonly textOpts:fabric.IITextOptions;
	tabObjects:fabric.IObject[];

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

	currentTab:ICanvasTab = null;

	switchTab(tab:ICanvasTab) {
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

class BuilderTab extends ICanvasTab {

	static make(canvas:fabric.ICanvas) {
		return new BuilderTab(canvas);
	}

	startPiece:BasicPuzzlePiece;
	totalCanvasHeight:number;
	maxCols:number;

	constructor(canvas:fabric.ICanvas) {
		super(canvas);
		separatorLine.set('visible', true);

		const startPiece = BasicPuzzlePiece.make(canvas, {
			fill : '#c2f0c2',
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

		const srcLangDescripts = getSrcLangDescripts(qcertLanguages());
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
		return "Builder";
	}

	getRectOptions() {
		return {fill:'orange'};
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

class InputTab extends ICanvasTab {
	titleTextElement:Node;
	inputTabElement:HTMLElement;
	queryInput:HTMLElement;
	defaultTitleTextElement:Node;

	static make(canvas:fabric.ICanvas) {
		return new InputTab(canvas);
	}

	constructor(canvas:fabric.ICanvas) {
		super(canvas);
		this.inputTabElement = document.getElementById("input-tab");
		this.titleTextElement = document.getElementById("input-tab-lang-title");
		this.defaultTitleTextElement = <HTMLElement>this.titleTextElement.cloneNode(true);
		this.queryInput = document.getElementById("input-tab-query-input");
	}

	getLabel() {
		return "Input";
	}
	
	getRectOptions() {
		return {fill:'orange'};
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
		const titleElem = document.createElement('h1');
		titleElem.style.textAlign = 'center';
		titleElem.appendChild(document.createTextNode("Input Language: " + piece.langid + " [" + piece.langdescription + "]"));
		this.titleTextElement.appendChild(titleElem);
	}

	update() {
		const srcpiece = InputTab.getSrcLanguagePiece();
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

function getPipelineLangs():{id:QcertLanguage,explicit:boolean}[] {
	return getPipelinePieces().map(function (piece) {
		if('langid' in piece) {
			return {id:(<any>piece).langid, explicit:! piece.isTransient()};
		} else {
			return undefined;
		}
	});
}

// function expandLangsPath(path:QcertLanguage[]):{id:QcertLanguage,explicit:boolean}[] {
// 	let expanded = [];
// 	const pathLen = path.length;
// 	if(path == null || pathLen == 0) {
// 		return expanded;
// 	}

// 	let prev = path[0];
// 	expanded.push({id:prev, explicit:true});
// 	for(let i = 1; i < pathLen; i++) {
// 		const cur = path[i];
// 		const curPath = qcertLanguagesPath({
// 			source: prev,
// 			target:cur
// 		}).path;
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

function getLanguageMarkedLabel(langpack:{id:QcertLanguage, explicit:boolean}):string {
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

class CompileTab extends ICanvasTab {

	static make(canvas:fabric.ICanvas) {
		return new CompileTab(canvas);
	}

	constructor(canvas:fabric.ICanvas) {
		super(canvas);
	}
	getLabel() {
		return "Compile";
	}

	getRectOptions() {
		return {fill:'orange'};
	}

	/* We should save and compare against the old workspace state
	 * so that we don't recompile everything everytime we come back to this tab
	 * Maybe create a state manager,
	 * and allow each tab to register with it and save/restore state as needed
	 *
	 * 
	 */

	setError(msg:string) {
		console.log(msg);
	}

    show() {
		this.canvas.selection = false;
		const langs = getPipelineLangs();
		const optims = getOptimConfig();
		const srcInput = getSrcInput();
        const schemaInput = getSchemaInput();

        const compiling = new fabric.Text("[ Compiling query ]");
        const theCanvas = this.canvas;
        theCanvas.add(compiling);
        theCanvas.renderAll();

        if (srcInput.length == 0) {
            ensureFit(theCanvas, compiling, "[ Query contents have not been specified ]");
            return;
        }

        const path = langs.map(x => x.id);
		if (path.length <= 2) {
            ensureFit(theCanvas, compiling, "[ No source and/or target language specified ]");
			return;
		}

		const middlePath = path.slice(1,-1);
        
        const handler = function(resultPack: QcertResult) {
            compiledQuery = resultPack.result;
            ensureFit(theCanvas, compiling, compiledQuery);
        }
        
		qcertPreCompile({
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
            input:undefined
		  }, handler); 
	}
}

class ExecTab extends ICanvasTab {

    static make(canvas:fabric.ICanvas) {
        return new ExecTab(canvas);
    }

    constructor(canvas:fabric.ICanvas) {
        super(canvas);
    }

    getLabel() {
        return "Execute";
    }

    getRectOptions() {
        return {fill:'orange'};
    }

    setError(msg:string) {
        console.log(msg);
    }

    show() {
        this.canvas.selection = false;
        const langs = getPipelineLangs();
        const path = langs.map(x => x.id);

        executing = new fabric.Text("[ Executing query ]");
        this.canvas.add(executing);
        if (path.length <= 2) {
            ensureFit(this.canvas, executing, "[ No source and/or target language specified ]");
            return;
        }

        const dataInput = getIOInput();
        if (dataInput.length == 0) {
            ensureFit(this.canvas, executing, "[ No input data specified ]");
            return;
        }
        
        // expose the kill button
        document.getElementById("kill-button").style.display = "block";
        
        // Additional inputs
        const target = langs[langs.length-1].id;
        const schemaInput = getSchemaInput();
        
        // Handle according to target language            
        if (target != "js")
            // TODO the kill button is ineffective for this case
            this.compileForEval(path, executing, getSrcInput(), schemaInput, dataInput);
        else
            this.performJsEvaluation(dataInput, schemaInput);

        // hide the kill button
        document.getElementById("kill-button").style.display = "none";
    }
    
    performJsEvaluation(inputString:string, schemaText:string) {
        if (compiledQuery == null) {
            ensureFit(this.canvas, executing, "[ The query has not been compiled ]");
            return;
        }
    
        // Processing is delegated to a web-worker
        try {
            // Worker variable is global (also executing and executingCanvas), making it (them) accessible to the killButton() function
            worker = new Worker("evalWorker.js");
            executingCanvas = this.canvas;
            worker.onmessage = function(e) {
                ensureFit(executingCanvas, executing, e.data);
            }
            worker.onerror = function(e) {
                ensureFit(executingCanvas, executing, e.message);
            }
            worker.postMessage([inputString, schemaText, compiledQuery]);
        } catch (err) {
            ensureFit(this.canvas, executing, err.message);
        }
    }

    compileForEval(path:string[], executing:any, srcInput:string, schemaInput:string, dataInput:string) {
        if (srcInput.length == 0) {
            ensureFit(this.canvas, executing, "[ Query contents have not been specified ]");
            return;
        }
        
        const theCanvas = this.canvas;
        var handler = function(compilationResult: QcertResult) {
            ensureFit(theCanvas, executing, compilationResult.eval);
        }
        const middlePath = path.slice(1,-1);
        qcertPreCompile({   
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
            eval: true,
            input: dataInput
          }, handler); 
    }
}

const coqdocBaseURL = 'https://querycert.github.io/sigmod17/';
function makeLemmaURL(base:string, lemma:string) {
	let url = coqdocBaseURL + "Qcert." + base + ".html";
	if(lemma != undefined) {
		url = url + "#" + lemma;
	}
	return url;
}

function makeOptimElement(modulebase:string, o:QcertOptimStepDescription):HTMLLIElement {
	const entry = document.createElement('li');
	entry.classList.add("optim-list");
	entry.appendChild(document.createTextNode(o.name));
	const lemmaLink = document.createElement('a');
	lemmaLink.href = makeLemmaURL(modulebase, o.lemma);
	lemmaLink.appendChild(document.createTextNode('✿'));
	lemmaLink.classList.add('lemma-link');
	entry.appendChild(lemmaLink);
	entry.title = o.description;
	entry.setAttribute('data-id', o.name);
	return entry;
}

function makeAvailableOptimElement(modulebase:string, o:QcertOptimStepDescription):HTMLLIElement {
	return makeOptimElement(modulebase, o);
}

function addRemoveButton(elem:HTMLElement) {
	const removenode = document.createElement('i');
	removenode.classList.add('js-remove');
	removenode.appendChild(document.createTextNode('✖'));
	elem.appendChild(removenode);
}

function makeSimpleOptimElement(optim:string) {
	const entry = document.createElement('li');
	entry.classList.add('optim-list');

	entry.appendChild(document.createTextNode(optim));
	return entry;
}

function makePhaseOptimElement(
	modulebase:string,
	optims:QcertOptimStepDescription[],
	optim:string):HTMLLIElement {

	const fulloptim = findFirstWithField(optims, 'name', optim);
	const entry = fulloptim ? makeOptimElement(modulebase, fulloptim) : makeSimpleOptimElement(optim);
	addRemoveButton(entry);
	return entry;
}

class OptimPhaseTab extends ICanvasDynamicTab {
	static make(canvas:fabric.ICanvas,
		parentDiv:HTMLElement, 
		modulebase:string,
		optims:QcertOptimStepDescription[],

		phase:QcertOptimPhase, 
		options:{color:string, top?:number}):OptimPhaseTab {
		return new OptimPhaseTab(canvas, parentDiv, modulebase, optims, phase, options);
	}

	constructor(canvas:fabric.ICanvas,
		div:HTMLElement,  
		modulebase:string,
		optims:QcertOptimStepDescription[],

		phase:QcertOptimPhase,
		options:{color:string, top?:number}) {
		
		super(canvas);
		this.name = phase.name;
		this.iter = phase.iter;
		this.top = options.top || 0;
		this.color = options.color || 'orange';

		//this.body = document.getElementsByTagName("body")[0];
		this.parentDiv = div;
		const newdiv = document.createElement('div');
		this.optimDiv = newdiv;


		const divTitle = document.createElement('h3');
		divTitle.style.cssFloat = 'center';
		const titlenodetext = (num:number) => "Currently selected optimizations (" + num + ")";
		const titlenode = document.createTextNode(titlenodetext(phase.optims.length));
		divTitle.appendChild(titlenode);
		newdiv.appendChild(divTitle);
		const divIterations = document.createElement('h4');
		divIterations.appendChild(document.createTextNode("These optimizations will be batched in " + phase.iter + " iterations "));
		newdiv.appendChild(divIterations);

		const listnode = document.createElement('ul');
		listnode.classList.add('optim-list');

		for(let i =0 ; i < phase.optims.length; i++) {
			listnode.appendChild(makePhaseOptimElement(modulebase, optims, phase.optims[i]));
		}

		function updateTitleContent() {
			titlenode.textContent = titlenodetext(listnode.childElementCount);
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
				updateTitleContent();
  			},
			onAdd: function (evt) {
				const item = evt.item;
				addRemoveButton(item);
			},
			onSort: function(evt) {
				updateTitleContent();
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

	getPhase():QcertOptimPhase {
		return {
			name:this.name,
			optims:this.sortable.toArray(),
			iter: this.iter
		}
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
	show() {
		this.parentDiv.appendChild(this.optimDiv);		

		//this.canvas.add(this.rect);
	}

	hide() {
		this.parentDiv.removeChild(this.optimDiv);
		//this.canvas.remove(this.rect);
	}
}

function optimPhaseMake(canvas:fabric.ICanvas, 	
	div:HTMLElement,
	module_base:string,
	optims:QcertOptimStepDescription[],
options:{color:string, top?:number}) {
	return function(phase:QcertOptimPhase) {
		return OptimPhaseTab.make(canvas, div, module_base, optims, phase, options);
	}

}

class OptimizationManager extends ICanvasTab {
	
	static make(canvas:fabric.ICanvas, 
				options:{rectOptions?:fabric.IRectOptions, textOptions?:fabric.IITextOptions, tabOrigin?:{left?:number, top?:number}}, 
				language:QcertLanguage,
				modulebase:string,
				optims:QcertOptimStepDescription[],
				cfg_phases:QcertOptimPhase[],
				startTab:number=-1):OptimizationManager {
					
		const tm = new OptimizationManager(canvas, options, language, modulebase, optims, cfg_phases);
		return tm;
	}

	language:QcertLanguage;
	optimTabs:OptimPhaseTab[];
	tabManager:TabManager;
	parentDiv:HTMLElement;
	topDiv:HTMLElement;
	phasesDiv:HTMLElement;

	rectOptions?:fabric.IRectOptions;
	textOptions?:fabric.IITextOptions;

	protected constructor(
		canvas:fabric.ICanvas, 
		options:{rectOptions?:fabric.IRectOptions, textOptions?:fabric.IITextOptions, tabOrigin?:{left?:number, top?:number}}, 
		language:QcertLanguage,
		module_base:string,
		optims:QcertOptimStepDescription[],
		cfg_phases:QcertOptimPhase[]) {

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
	
		this.optimTabs = cfg_phases.map(optimPhaseMake(canvas, leftdiv, module_base, optims, {color:'yellow', top:yoffset2}));

		this.tabManager = TabManager.make(canvas, 
				{
					label:language,
					rectOptions:options.rectOptions,
			 		textOptions:options.textOptions, 
				 	tabOrigin:options.tabOrigin
				}, this.optimTabs, 0);
		

	}

	getOptimConfig():QcertOptimConfig {
		return {
			language:this.language,
			phases:this.getConfigPhases()
		}
	}
	
	getConfigPhases():QcertOptimPhase[] {
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
	}

	hide() {
		this.tabManager.hide();
		this.parentDiv.removeChild(this.topDiv);		
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

function OptimizationsTabMake(canvas:fabric.ICanvas) {
	const yoffset = 60;
	const optims = qcertOptimList().optims;
	const defaults = qcertOptimDefaults().optims;

	const opts = {rectOptions:{fill:'green'}, tabOrigin:{top:yoffset}};	
	let optimTabs:OptimizationManager[] = [];
	for(let i=0; i < optims.length; i++) {
		const opt = optims[i];
		const cfg = findFirstWithField(defaults, 'language', opt.language.name);
		const cfg_phases = cfg === undefined ? [] : cfg.phases;

		optimTabs.push(OptimizationManager.make(canvas, opts, opt.language.name, opt.language.modulebase, opt.optims, cfg_phases));
	}
	globalOptimTabs = optimTabs;
	return TabManager.make(canvas, {label:"Optimizations", rectOptions:{fill:'orange'}}, optimTabs, 0);
}

function getOptimConfig():QcertOptimConfig[] {
	if(globalOptimTabs) {
		return globalOptimTabs.map((x) => x.getOptimConfig());
	} else {
		return [];
	}
}

const tabinitlist:((canvas:fabric.ICanvas)=>ICanvasTab)[] = [
	BuilderTab.make,
	OptimizationsTabMake,
	InputTab.make,
	CompileTab.make,
    ExecTab.make
];

function init():void {
	const maincanvas = new fabric.Canvas('main-canvas');
	const tabscanvas = new fabric.Canvas('tabs-canvas');

	const tabs = tabinitlist.map(function (elem) {
		return elem(maincanvas)
	});
	const tm = TabManager.make(tabscanvas, {label:"Q*cert"}, tabs, 0);
	tm.show();
	tabscanvas.renderAll();
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
    var delimiter = (<HTMLTextAreaElement>document.getElementById("delimiter")).value; 
    var schema = JSON.parse((<HTMLTextAreaElement>document.getElementById("input-tab-query-schema-text")).value);
    var toSend = JSON.stringify({schema: schema, delimiter: delimiter, data: readFiles});
    var process = function(result) {
        document.getElementById("input-tab-query-io-text").innerHTML = result;
    }
    var result = preProcess(toSend, "csv2JSON", process);
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
                if (isSchema && isSQLSchema(contents))
                    convertSQLSchema(contents, outputElem);
                else
                    outputElem.value = contents;
            }
            reader.readAsText(file);
        }
    }
}

// Determine if a String contains a SQL schema.  Not intended to be foolproof but just to discriminate the two supported schema
// notations (SQL and JSON) when the input is at least mostly valid.
function isSQLSchema(schemaText:string) : boolean {
    /* A SQL schema should have the word "create" in it but SQL is case insensitive  */
    var create = schemaText.search(/create/i);
    if (create < 0)
        return false;
    var brace = schemaText.indexOf('{');
    if (brace >= 0 && brace < create)
        /* Word create is coincidentally appearing inside what is probably a JSON schema */
        return false;
    /* Looking more like SQL.  Drop any blanks that follow 'create' */
    var balance = schemaText.substring(create + 6).trim();
    /* The next word must be 'table' (case insensitive) */
    var table = balance.search(/table/i);
    return table == 0;
}

function convertSQLSchema(toConvert:string, outputElem:HTMLTextAreaElement) {
    var process = function(result:string) {
        outputElem.value = result;
    }
    var result = preProcess(toConvert, "sqlSchema2JSON", process);
}

function handleFileDrop(output:string, event:DragEvent) {
	event.stopPropagation();
  	event.preventDefault();
	var dt = event.dataTransfer;
  	var files = dt.files;
	handleFile(output, false, files);
}

function getSrcInput():string {
	const elem = <HTMLTextAreaElement>document.getElementById('input-tab-query-src-text');
	return elem.value;
}

function getSchemaInput():string {
    const elem = <HTMLTextAreaElement>document.getElementById('input-tab-query-schema-text');
    return elem.value;
}

function getIOInput():string {
	const elem = <HTMLTextAreaElement>document.getElementById('input-tab-query-io-text');
	return elem.value;
}