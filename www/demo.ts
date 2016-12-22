
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

	const gridRows = 3;
	const pipelineRow = 1;

	const gridOffset:fabric.IPoint = new fabric.Point(20,20);
	const canvasHeightInteractive = gridRows*pieceheight+gridOffset.y*2;
	// TODO: This number should be automatically calculated
	const canvasHeightChooser = 400;

	// we should set canvas width appropriately
	let totalCanvasWidth = 1000;
	const totalCanvasHeight = canvasHeightInteractive + canvasHeightChooser;

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

interface IPuzzlePiece extends fabric.IObject {
	// this should be in the fabric ts file
	canvas:fabric.IStaticCanvas;

	// new stuff
	isSourcePiece?:boolean;
	movePlace?:{left:number, top:number};
	langid:string;
	langdescription:string;
	tooltipObj?:fabric.IObject;
	puzzleOffset:fabric.IPoint;
	getGridPoint:()=>fabric.IPoint;
	setGridPoint:(point:fabric.IPoint)=>void;
	setGridCoords:(x:number, y:number)=>void;

	// these are to help avoid accidentally setting
	// left or top without calling setCoords() after as required
	mySetLeft:(x:number)=>void;
	mySetTop:(y:number)=>void;
	mySetLeftAndTop:(x:number, y:number)=>void;
	readonly left:number;
	readonly top:number;
}

// The class for a puzzle piece object


interface StringMap<V> {
	[K: string]: V;
}

var sourcePieces:StringMap<IPuzzlePiece> = {};
var placedPieces:IPuzzlePiece[][] = [];



function makePuzzlePiece(options):any {
	    options || (options = { });
	options.width = piecewidth;
	options.height = pieceheight;

	const puzzleSides:PuzzleSides = options.sides || {};
	const puzzleLeft = puzzleSides.left || 0;
	const puzzleRight = puzzleSides.right || 0;
	const puzzleTop = puzzleSides.top || 0;
	const puzzleBottom = puzzleSides.bottom || 0;

	function calcPuzzleEdgeOffset(side:number):number {
		if(side < 0) {
			return 9;
		} else if(side > 0) {
			return 20;
		} else {
			return 0;
		}
	}
	const puzzleOffsetPoint = new fabric.Point(	calcPuzzleEdgeOffset(puzzleLeft),
						calcPuzzleEdgeOffset(puzzleTop));


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

	const group:any = new fabric.Group([path, text],
	{
		hasControls:false,
		hasBorders:false
	});

	group.puzzleOffset = puzzleOffsetPoint;
	
	group.getGridPoint = function():fabric.IPoint {
		return new fabric.Point(
			Math.round((this.left + this.puzzleOffset.x - gridOffset.x) / piecewidth),
			Math.round((this.top + this.puzzleOffset.y - gridOffset.y) / pieceheight));
	};

	group.setGridPoint = function(point:fabric.IPoint):void {
		this.setGridCoords(point.x, point.y);
	};

	group.setGridCoords = function(x:number, y:number):void {
		this.left = x * piecewidth - this.puzzleOffset.x + gridOffset.x;
		this.top = y * pieceheight - this.puzzleOffset.y + gridOffset.y;
		this.setCoords();
	};

	return group;
}

function mkSourcePiece(options):IPuzzlePiece {
	const group = makePuzzlePiece(options);
	
	
	group.isSourcePiece = true;
	group.langid = options.langid;
	group.langdescription = options.langdescription;

	group.mySetLeft = function(x:number) {
	  group.left = x;
	  this.setCoords();
  	};
  	group.mySetTop = function(y:number) {
	  this.top = y;
	  this.setCoords();
  	};
  	group.mySetLeftAndTop = function(x:number, y:number) {
	  this.left = x;
	  this.top = y;
	  this.setCoords();
  	};

	// snap to grid



	const piece:IPuzzlePiece = group;
	piece.hoverCursor = 'grab';
	(<any>piece).moveCursor = 'grabbing';

	// TODO: when me move something, shift things to the right back over it (to the left)
	// be careful how that interacts with the shift right code!
	// TODO: work on getting things to move out of the way
	// track what we were over last / are over now
	// and use that to track what is going on
	// once that is working, change the code to move things over 
	// to use animations to look smooth

	function mousedownfunc() {
		piece.set({
			opacity:.5
		});
		// clear any tooltip
		if('tooltipObj' in piece) {
			piece.canvas.remove(piece.tooltipObj);
			delete piece.tooltipObj;
		}

		if(piece.isSourcePiece) {
			// create a new copy of this piece
			var copyOfSelf = mkSourcePiece(options);
			// and make it the new "canonical" source piece
			sourcePieces[options.langid] = copyOfSelf;
			piece.canvas.add(copyOfSelf);

			// now make this piece into a non source piece
			piece.isSourcePiece = false;
		} else {
			// update the placed grid
			const topentry = Math.round(piece.top / pieceheight);
			const leftentry = Math.round(piece.left / piecewidth);
			
			delete placedPieces[topentry][leftentry];
		}
	};

	piece.on('mousedown', mousedownfunc);

	piece.on('mouseup', function() {
		piece.set({
			opacity:1
		});
		const gridp = piece.getGridPoint();
		const leftentry = gridp.x;
		const topentry = gridp.y;

		piece.setGridPoint(gridp);
	
		if(!piece.isSourcePiece) {
			// fix this to use grid coordinates
			if(piece.top >= canvasHeightInteractive) {
				piece.canvas.remove(piece);
			}

			// update the placed grid
			if('movePlace' in piece) {
				// finalize the moved pieces in their new positions
				const prow = placedPieces[topentry];
				if(! (prow === undefined)) {
					let curleft = leftentry;
					let curleftval = prow[leftentry];
					while(! (curleftval === undefined)) {
						let nextleft = curleft+1;
						let nextleftval = prow[nextleft];

						prow[nextleft] = curleftval;
						curleft = nextleft;
						curleftval = nextleftval;
					}
					ensureCanvasInteractivePieceWidth(piece.canvas, curleft+1);
					prow[leftentry] = undefined;
				}
				delete piece['movePlace'];
			}
			if(topentry >= placedPieces.length || placedPieces[topentry] === undefined) {
				placedPieces[topentry] = [];
			}
			const topplaces = placedPieces[topentry];
			if(leftentry >= topplaces.length || topplaces[leftentry] === undefined) {
				topplaces[leftentry] = piece;
			}
		}
//		piece.canvas.renderAll();
	});
	piece.on('moving', function() {
		const gridp = piece.getGridPoint();
		const leftentry = gridp.x;
		const topentry = gridp.y;


		if('movePlace' in piece) {
			if(piece.movePlace.left == leftentry && piece.movePlace.top == topentry) {
				// still over the same grid spot
				return;
			}
			// otherwise, we moved.  We need to put back anything we moved out of the way
			const oldtop = piece.movePlace.top;
			const prow = placedPieces[oldtop];
			if(! (prow === undefined)) {
				var oldleft = piece.movePlace.left;
				while(true) {
					let mp = prow[oldleft];
					if(mp === undefined) {
						break;
					}
					mp.setGridCoords(oldleft, oldtop);
					oldleft = oldleft + 1;
				}
			}
		}
		piece.movePlace = {top:topentry, left:leftentry};
		const prow = placedPieces[topentry];
		if(! (prow === undefined)) {
			var curleft = leftentry;
			while(true) {
				let mp = prow[curleft];
				if(mp === undefined) {
					break;
				}
				mp.setGridCoords(curleft+1, topentry);
				curleft = curleft + 1;
			}
		}
	});
	
	piece.on('mouseover', function() {
		if(piece.isSourcePiece) {
			if(! ('tooltipObj' in piece)) {

				// calculate where it should appear.
				const text = new fabric.IText(piece.langdescription, 
				{ left: 0, 
					top: 0,
					fill:'black',
					fontSize:40,
					editable:false
					});

				const tooltipOffset:fabric.IPoint = new fabric.Point(10, 10);

				let boundingBox = text.getBoundingRect();
				const maxwidth = piece.canvas.getWidth()*3/4;

				// if needed, shrink the font so that the text
				// is not too large
				while(boundingBox.width > maxwidth) {
					text.setFontSize(text.getFontSize()-2);
					text.setCoords();
					boundingBox = text.getBoundingRect();
				}
				let piecemid = piece.left + Math.round(piecewidth/2);
				
				let boxleft = piecemid - Math.round(boundingBox.width / 2);
				if(boxleft < 0) {
					boxleft = 0;
				} else {
					let tryright = piecemid + Math.round(boundingBox.width / 2);
					tryright = Math.min(tryright, piece.canvas.getWidth());
					boxleft = tryright - boundingBox.width;
				}

				let boxtop = piece.top - boundingBox.height - tooltipOffset.y;
				if(boxtop < 0) {
					boxtop = piece.top + piece.height + tooltipOffset.y;
				}

				text.originX = 'left';
				text.left = boxleft;
				text.originY = 'top';
				text.top = boxtop;
				text.setCoords();
				const box = new fabric.Rect(text.getBoundingRect());
				box.setFill('#EEEEEE');
				const group = new fabric.Group([box, text]);
				piece.tooltipObj = group;
				piece.canvas.add(group);
			}
		}
	});
	piece.on('mouseout', function() {
		if('tooltipObj' in piece) {
			piece.canvas.remove(piece.tooltipObj);
			delete piece.tooltipObj;
		}
	});

	return piece;
}



function init() {
    var canvas = new fabric.Canvas('main-canvas');
	// TODO: at some point enable this
	// but upon creation remove any inappropriate (source) elements
	// and set up the mouse up/down/hover code
	// taking care that the algorithm may now need to move things multiple spaces
	canvas.selection = false;
	canvas.hoverCursor = 'pointer';

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
	
	canvas.add(separatorLine);
	separatorLine.set('visible', true);
	// disable group selection
	//canvas.selection = false;

	// create the start piece
	// note that the start piece is meant to have a "real" piece put on top of it by the user
	var startPiece = makePuzzlePiece({
		fill : '#c2f0c2',
		label : 'start',
		sides : {right:-1},
		hasControls : false,
		selectable : false,
		evented : false
	});
	startPiece.setGridCoords(0, 1);
	startPiece.set({
		hasControls : false,
		selectable: false
	});
	startPiece.hoverCursor = 'auto';

	canvas.add(startPiece);

	const runText = new fabric.Text('R\nu\nn', {
		left:0,
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
		height:pieceheight});
	const runGroup = new fabric.Group([runRect, runText]);
	runGroup.set({
		hasControls:false,
		selectable:false
	});

	canvas.add(runGroup);

	const srcLangDescripts = getSrcLangDescripts(qcertLanguages());
	let maxCols:number = 0;
	// create the list of languages that can be dragged onto the canvas
	for(var srcrow=0; srcrow < srcLangDescripts.length; srcrow++) {
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
			let piece = mkSourcePiece(colelem);
			sourcePieces[colelem.langid] = piece;
			canvas.add(piece);
		}
		maxCols = Math.max(srccol, maxCols);
	}
	// make sure the canvas is wide enough
	ensureCanvasSourcePieceWidth(canvas, maxCols);

	canvas.setHeight(totalCanvasHeight);

	canvas.renderAll();
}
