type SourceLanguageGroups = {
		frontend:[{langid, label}], 
		intermediate:[{langid, label}], 
		backend:[{langid, label}]};

declare function languages(): SourceLanguageGroups;
