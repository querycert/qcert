
// constants
// these must remain 100 for the puzzle piece path stuff to work out
	const piecewidth = 100;
	const pieceheight = 100;
	const canvasHeightPipeline = 100
	const canvasHeightInteractive = 400;
	const canvasHeightChooser = 300;
	// we should set canvas width appropriately
	const totalCanvasWidth = 1000;
	const totalCanvasHeight = canvasHeightInteractive + canvasHeightChooser;

	// The set of languages and their properties
	const acrossSides = {left:1, right:-1};
	const srcLangDescripts = [
		null,
		[null,
		{label:'OQL', fill:'#FFCC99', sides:acrossSides},
		null,
		{label:'SQL', fill:'#FFCC99', sides:acrossSides}]];

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

// The class for a puzzle piece object
var PuzzlePiece = fabric.util.createClass(fabric.Rect, {

  type: 'puzzlePiece',

  initialize: function(options) {
    options || (options = { });
	options.width = piecewidth;
	options.height = pieceheight;
    this.callSuper('initialize', options);
    this.set('label', options.label || '');

	const puzzleSides = options.sides || {};
	const puzzleLeft = puzzleSides.left || 0;
	const puzzleRight = puzzleSides.right || 0;
	const puzzleTop = puzzleSides.top || 0;
	const puzzleBottom = puzzleSides.bottom || 0;

	var path = new fabric.Path(getMask(1, puzzleTop, puzzleRight, puzzleBottom, puzzleLeft));
	path.centeredScaling = true;
    path.scale(1);

    //path.selectable = true;
    path.originX = 'center';
    path.originY = 'center';
	this.puzzlePath = path;
	this.set('clipTo', function (ctxt) {
	 		path._render(ctxt);
	});

  },

  toObject: function() {
    return fabric.util.object.extend(this.callSuper('toObject'), {
      label: this.get('label')
    });
  },

  _render: function(ctx) {
    this.callSuper('_render', ctx);
    ctx.font = '30px Helvetica';
    ctx.fillStyle = '#333';
	ctx.textAlign='center';
	ctx.textStyle='bold';
    ctx.fillText(this.label, -this.width/2+50, -this.height/2 + 30);
  }
});


function mkSourcePiece(options) {

	var piece = new PuzzlePiece({
		left : (options.col || 0)*piecewidth,
		top : canvasHeightInteractive + ((options.row || 0)*pieceheight),
		fill : options.fill || 'purple',
		label : options.label,
		sides : options.sides || {},
		hasControls : false
	});
	piece.on('moving', function() { 
		piece.set({
		left: Math.round(piece.left / piecewidth) * piecewidth,
		top: Math.round(piece.top / piecewidth) * piecewidth
		});
	});
	piece.on('mousedown', function() {
		piece.set({
			opacity:.5
		})
	});
	piece.on('mouseup', function() {
		piece.set({
			opacity:1
		})
	});
	//piece.off('moving');
	return piece;
}



function init() {
    var canvas = new fabric.Canvas('main-canvas');

	// first, lets draw the boundary between the interactive and the selections
	const separatorLine = new fabric.Line([ 0, canvasHeightInteractive, totalCanvasWidth, canvasHeightInteractive], { stroke: '#ccc', selectable: false });
	
	canvas.add(separatorLine);
	separatorLine.set('visible', true);
	// disable group selection
	//canvas.selection = false;

	// create the start piece
	var startPiece = new PuzzlePiece({
		left : 10,
		top : canvasHeightPipeline,
		fill : 'green',
		label : 'start',
		sides : {right:-1},
		hasControls : false,
		selectable : false,
		evented : false
	});
	canvas.add(startPiece);

	// create the list of languages that can be dragged onto the canvas
	var sourceCollection = [];
	for(var srcrow=0; srcrow < srcLangDescripts.length; srcrow++) {
		let rowelem = srcLangDescripts[srcrow];
		if(rowelem == null) {
			continue;
		}
		for(var srccol=0; srccol < rowelem.length; srccol++) {
			let colelem = rowelem[srccol];
			if(colelem == null) {
				continue;
			}

			colelem.row = srcrow;
			colelem.col = srccol;
			let piece = mkSourcePiece(colelem);
			sourceCollection.push(piece);
			canvas.add(piece);
		}
	}

    // // create grid
    // for (var i = 0; i < (600 / grid); i++) {
    //   canvas.add(new fabric.Line([ i * grid, 0, i * grid, 600], { stroke: '#ccc', selectable: false }));
    //   canvas.add(new fabric.Line([ 0, i * grid, 600, i * grid], { stroke: '#ccc', selectable: false }))
    // }

	// sourceCollection[1].set({
	// 	clipTo: function (ctxt) {
	// 		path._render(ctxt);
	// 	}
	// });
	canvas.renderAll();
}
