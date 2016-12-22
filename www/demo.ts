
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
	label:string;
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

// These are two critical arrays for the buider
// This is the collection of source pieces
var sourcePieces:StringMap<IPuzzlePiece> = {};
// This is the matrix of pieces that are in the grid
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


function mkSourcePiece(options):IPuzzlePiece {
	const group = makePuzzlePiece(options);
	
	
	group.isSourcePiece = true;
	group.langid = options.langid;
	group.label = options.label;
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

				const tip = makeToolTip(
					piece.langdescription,
					piece.canvas,
					{left:piece.left, top:piece.top, width:piecewidth, height:pieceheight},
					new fabric.Point(10, 10),
				 	{fill:'black', fontSize:40}, 
					{fill:'#EEEEEE'});
				
				piece.tooltipObj = tip;
				piece.canvas.add(tip);
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

interface ICanvasTab {
       label:string;
       rectOptions?:fabric.IRectOptions;
       textOptions?:fabric.ITextOptions;
       show():void;
       hide():void;
	   canvasObj?:fabric.IObject;
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

function init_builder(canvas:fabric.ICanvas):ICanvasTab {
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
	startPiece.setGridCoords(0, pipelineRow);
	startPiece.set({
		hasControls : false,
		selectable: false
	});
	startPiece.hoverCursor = 'auto';
	

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
			let piece = mkSourcePiece(colelem);
			sourcePieces[colelem.langid] = piece;
		}
		maxCols = Math.max(srccol, maxCols);
	}

	const canvasHeightChooser = srcrow;
	const totalCanvasHeight = getSourceTop(srcrow)-15;


	const canvasElement = document.getElementById('main-canvas');
	const tab:ICanvasTab = {
              label:"Builder",
               rectOptions:{fill:'orange'},
               show:function() {
				   	canvas.selection = false;
					canvas.hoverCursor = 'pointer';

					canvas.add(startPiece);
					//canvas.add(runGroup);
					canvas.add(separatorLine);

					// add the source pieces
					for(let piece in sourcePieces) {
						canvas.add(sourcePieces[piece]);
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
									canvas.add(piece);
								}
							}
						}
					}
					// make sure the canvas is wide enough
					ensureCanvasSourcePieceWidth(canvas, maxCols);
					// TODO: also make sure that it is wide enough for the pieces in the grid
					canvas.setHeight(totalCanvasHeight);
					canvas.renderAll();
				},
        		hide:function() {
                       canvas.clear();
               }
       };
	return tab;
}

function init_input(canvas:fabric.ICanvas):ICanvasTab {
		const rect = new fabric.Rect({
		left: 10, top: 5, width:200, height:50, fill:'purple',
		hasBorders:false, 
		hasControls:false,
		selectable:false
       });
       
       const tab:ICanvasTab = {
               label:"Input",
               rectOptions:{fill:'orange'},
               show:function() {
				    canvas.selection = false;
                    canvas.add(rect);
               },
               hide:function() {
                       canvas.clear();                
               }
       };
	   return tab;
}

function makeTab(canvas:fabric.IStaticCanvas, tab:ICanvasTab, top:number, left:number):fabric.IObject {
       const ropts = fabric.util.object.clone(defaultTabRectOpts);
	   fabric.util.object.extend(ropts, tab.rectOptions || {});

       ropts.left = left;
       ropts.top = top;
       ropts.editable = false;
       ropts.height = ropts.height || 50;
       ropts.width = ropts.width || 200;
       const box = new fabric.Rect(ropts);


	   const topts = fabric.util.object.clone(defaultTabTextOpts)
	   fabric.util.object.extend(topts, tab.textOptions || {});
       topts.left = 0;
       topts.top = 0;
       topts.editable = false;
       const text = new fabric.IText(tab.label, topts);
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

function getPipelinePieces():IPuzzlePiece[] {
	const prow = placedPieces[pipelineRow];
	const path = [];
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

function getPipelineLangs():QcertLanguage[] {
	return getPipelinePieces().map(function (piece) {
				return piece.langid;
	});
}

function expandLangsPath(path:QcertLanguage[]):{id:QcertLanguage,explicit:boolean}[] {
	let expanded = [];
	const pathLen = path.length;
	if(path == null || pathLen == 0) {
		return expanded;
	}

	let prev = path[0];
	expanded.push({id:prev, explicit:true});
	for(let i = 1; i < pathLen; i++) {
		const cur = path[i];
		const curPath = qcertLanguagesPath({
			source: prev,
			target:cur
		}).path;
		const curPathLen = curPath.length;

		if(curPath == null 
		|| curPathLen == 0
		|| (curPathLen == 1 && curPath[0] == "error")) {
			expanded.push("error");
		} else {
			for(let j = 1; j < curPathLen; j++) {
				expanded.push({id:curPath[j], explicit:(j+1)==curPathLen});
			}
		}
		prev = cur;
	}

	return expanded;
}

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

function init_path(canvas:fabric.ICanvas):ICanvasTab {

       const tab:ICanvasTab = {
               label:"Path",
               rectOptions:{fill:'orange'},
               show:function() {
				    canvas.selection = false;
					const langs = getPipelineLangs();
					const expanded = expandLangsPath(langs);
					const path = expanded.map(getLanguageMarkedLabel).join(" -> ");

					const txt = new fabric.Text(path, {
						left: 10, top: 5, width:200, height:50, fill:'purple'
					});
					

                    canvas.add(txt);
               },
               hide:function() {
                       canvas.clear();                
               }
       };
	   return tab;
}

const tabinitlist:((canvas:fabric.ICanvas)=>ICanvasTab)[] = [
	init_builder,
	init_input,
	init_path
];

function init():void {
	const maincanvas = new fabric.Canvas('main-canvas');
	const tabscanvas = new fabric.Canvas('tabs-canvas');

	const tabs = tabinitlist.map(function (elem) {
		return elem(maincanvas)
	});
	init_tabs(tabscanvas, tabs);
	switchTab(tabs[0]);
	tabscanvas.renderAll();
}

