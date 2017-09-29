import { Config, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = {
    whisk: {
	namespace: string;
	api_key: string;
	apihost: string;
    };
    cloudant: {
	username: string;
	password: string;
    }
    pkgname: string;
    action: string;
    querycode: Designs;
}

const main = async (params:ListIn) : Promise<ListIn> => {
    const whisk = params.whisk;
    const cloudant = params.cloudant;
    const pkgname: string = params.pkgname;
    const action: string = params.action;
    const querycode: Designs = params.querycode;

    const linkharness = (str:string):string => {
	const re = /\[HARNESS\]/g;
	return str.replace(re, runtime);
    }

    const linkedpost = linkharness(querycode.post);
    var linkeddesigns = []
    for (var i = 0; i < querycode.designs.length; i++) {
	const d = querycode.designs[i]
	const views = d.design.views
	for (var key in views) {
	    if (views.hasOwnProperty(key)) {
		views[key] = { 'dbcopy' : views[key].dbcopy,
			       'dbdefault' : linkharness(views[key].dbdefault),
			       'map' : linkharness(views[key].map),
			       'reduce' : linkharness(views[key].reduce) }
	    }
	}
	linkeddesigns.push({'dbname':d.dbname, 'design':{'views':views}})
    }
    const linkedcode =
	  { 'designs': linkeddesigns,
	    'post': linkedpost,
	    'post_input': querycode.post_input };
    const linkedquerycode =
	  { 'whisk' : whisk,
	    'cloudant' : cloudant,
	    'pkgname' : pkgname,
	    'action' : action,
	    'querycode' : linkedcode }
    
    return linkedquerycode;

}

const failure = (err) => {
    return { error: err }
}
