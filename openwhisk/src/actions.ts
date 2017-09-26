
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
	    'cloudant-undeploy': {
		sequence: "qcert/cloudant-undeploy-views,qcert/cloudant-undeploy-postproc",
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
	    'cloudant-undeploy-views': {
		location: path.resolve(__dirname, '.', 'cloudant-undeploy-views.js'),
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
	    'cloudant-undeploy-postproc': {
		location: path.resolve(__dirname, '.', 'cloudant-undeploy-postproc.js'),
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
