
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


function makeTab(canvas:fabric.IStaticCanvas, tab:ICanvasTab, top:number, left:number):fabric.IObject {
       const ropts = fabric.util.object.clone(defaultTabRectOpts);
	   fabric.util.object.extend(ropts, tab.getRectOptions() || {});

       ropts.left = left;
       ropts.top = top;
       ropts.editable = false;
       ropts.height = ropts.height || 50;
       ropts.width = ropts.width || 200;
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

let currentTab:ICanvasTab = null;
function switchTab(tab:ICanvasTab) {
	if(currentTab != null) {
		if('canvasObj' in currentTab) {
			const tabobj = currentTab.canvasObj;
			tabobj.setOpacity(0.3);
		}
		currentTab.hide();
	}
	currentTab = tab;
	tab.show();
	if('canvasObj' in tab) {
		const tabobj = tab.canvasObj;
		tabobj.setOpacity(1);
	}
}

function init_tabs(canvas:fabric.ICanvas, tabs:ICanvasTab[]) {
       canvas.selection = false;

       const tabTop = 5;
       let tabLeft = 10;

       for(let i=0; i < tabs.length; i++) {
               const itab = tabs[i];
               const tabgroup = makeTab(canvas, itab, tabTop, tabLeft);
               tabLeft += tabgroup.getBoundingRect().width;
               tabgroup.hoverCursor = 'pointer';
               tabgroup.on('selected', function() {
				   switchTab(itab);
               });

               canvas.add(tabgroup);
       }
}


class BuilderTab extends ICanvasTab {
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
	rect:fabric.IObject;

	constructor(canvas:fabric.ICanvas) {
		super(canvas);
		this.rect = new fabric.Rect({
			left: 10, top: 5, width:200, height:50, fill:'purple',
			hasBorders:false, 
			hasControls:false,
			selectable:false
       });
	}

	getLabel() {
		return "Input";
	}
	
	getRectOptions() {
		return {fill:'orange'};
	}

	show() {
		this.canvas.selection = false;
		this.canvas.add(this.rect);
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

class PathTab extends ICanvasTab {

	constructor(canvas:fabric.ICanvas) {
		super(canvas);
	}
	getLabel() {
		return "Path";
	}

	getRectOptions() {
		return {fill:'orange'};
	}

    show() {
		this.canvas.selection = false;
		const langs = getPipelineLangs();
		//const expanded = expandLangsPath(langs);
		const path = langs.map(getLanguageMarkedLabel).join(" -> ");

		const txt = new fabric.Text(path, {
			left: 10, top: 5, width:200, height:50, fill:'purple'
		});
		
		this.canvas.add(txt);
	}
}

class OptimizationsTab extends ICanvasTab {
	rect:fabric.IObject;

	constructor(canvas:fabric.ICanvas) {
		super(canvas);
		this.rect = new fabric.Rect({
			left: 10, top: 5, width:200, height:50, fill:'purple',
			hasBorders:false, 
			hasControls:false,
			selectable:false
       });
	}

	getLabel() {
		return "Optimizations";
	}
	
	getRectOptions() {
		return {fill:'orange'};
	}

	show() {
		this.canvas.selection = false;
		this.canvas.add(this.rect);
	}
}

const tabinitlist:(new (canvas:fabric.ICanvas)=>ICanvasTab)[] = [
	BuilderTab,
	InputTab,
	OptimizationsTab,
	PathTab
];

function init():void {
	const maincanvas = new fabric.Canvas('main-canvas');
	const tabscanvas = new fabric.Canvas('tabs-canvas');

	const tabs = tabinitlist.map(function (elem) {
		return new elem(maincanvas)
	});
	init_tabs(tabscanvas, tabs);
	switchTab(tabs[0]);
	tabscanvas.renderAll();
}
