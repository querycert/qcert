const fs = require("fs");

const quote_arg = function (arg) {
    return "'" + arg + "'";
}

const execute_command = function (command,args) {
    const exec = require('child_process').exec;
    var quoted_args = [ ];
    for (i=0;i < args.length;i++) {
	quoted_args.push(quote_arg(args[i])); 
    }
    child = exec(command+' '+quoted_args.join(' '), function (error, stdout, stderr) {
        if (stdout !== null){
            if (stdout !== "") process.stdout.write(stdout);
        }
        if (stderr !== null){
            if (stderr !== "") process.stdout.write('stderr: '+ stderr);
        }
        if (error !== null) {
            if (error !== "") process.stdout.write('exec error: ' + error);
        }
    });
}

module.exports = function () {
    return {
	execute: function(path) {
	    if (fs.existsSync(path)) {
		const command = "node " + path;
		execute_command(command,process.argv.slice(2));
	    } else {
		console.log('Missing file: ' + path + ', please compile.');
	    }
	}
    };
};

