type SourceLanguageGroups = {
		frontend:[{langid:string, label:string}], 
		intermediate:[{langid:string, label:string}], 
		backend:[{langid:string, label:string}]};

declare function languages(): SourceLanguageGroups;
