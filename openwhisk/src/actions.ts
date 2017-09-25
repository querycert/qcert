
export const config = () => {
  const path = require('path')

  const qcertDir = path.resolve(__dirname, '..', '..', '..')

  const deployConfig = {
    packages: {
      qcert: {
        actions: {
            'core-compile': {
		location: path.resolve(qcertDir, 'bin', 'qcertJS.js'),
		annotations: {
		    'web-export': true
		}
            },
	    'compile': {
		sequence: "qcert/preCompile,qcert/core-compile",
		annotations: {
		    'web-export': true
		}
            },
	    'cloudant-deploy': {
		sequence: "qcert/cloudant-deploy-views,qcert/cloudant-deploy-postproc",
		annotations: {
		    'web-export': true
		}
            },
	    'cloudant-deploy-views': {
		location: path.resolve(__dirname, '.', 'cloudant-deploy-views.js'),
		annotations: {
		    'web-export': true
		}
	    },
	    'cloudant-undeploy': {
		location: path.resolve(__dirname, '.', 'cloudant-undeploy.js'),
		annotations: {
		    'web-export': true
		}
	    },
	    'cloudant-deploy-postproc': {
		location: path.resolve(__dirname, '.', 'cloudant-deploy-postproc.js'),
		annotations: {
		    'web-export': true
		}
	    },
	    'cloudant-refresh': {
		location: path.resolve(__dirname, '.', 'cloudant-refresh.js'),
		annotations: {
		    'web-export': true
		}
	    }
        }
      }
    }
  }

  return deployConfig
}
