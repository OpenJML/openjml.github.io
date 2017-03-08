var app = angular.module('OpenJML', []);

var verificationServer  = "openjml.cs.ucf.edu";


var exampleProgram = "//\n// This program contains a coding error and one other possible error. \n// Can you find them?\n//\n\
public class MaybeAdd {\n \
    //@ requires a > 0;\n \
    //@ requires b > 0;\n \
    //@ ensures \\result == a+b;\n \
    public static int add(int a, int b){\n \
        return a-b;\n \
    }\n\
    \n\n\
    public static void main(String args[]){\n \
        System.out.println(add(2,3));\n \
    }\n \
}\n";
 
app.controller('LilVerifyCtrl', function ($scope, $sce, $timeout, $http) {


    var verified = false;

    $scope.verifyExampleProgram = function(){


        location.href='http://www.rise4fun.com/OpenJMLESC/MaybeAdd';

        if(1==1){
            return;
        }

	verified = true;
	$("#playButton").hide();
	
	// some animation
	$( "#codePreview pre" ).animate({
            height: 625
        }, 1000 );

	$( "#codePreview pre" ).append('<div align="center" style="margin-top: 50px"><img style="display: none;" src="/images/progress.gif" id="loading"/></div>');
	$( "#loading" ).fadeIn();

	
	$http({
	    url:'http://openjml.cs.ucf.edu/ExtendedStaticChecker/run',
	    data: {Source:exampleProgram},
	    method: 'POST',
	    headers: {'Content-Type': 'application/json'}
	}).
	    success(function(data, status, headers, config) {
		console.log(data);

		var response    = data;

		// find the markdown result
		var markdownContent = response.Outputs.filter(function(o){ return o.MimeType==="text/x-web-markdown";})[0].Value;
		var output = markdown.toHTML(markdownContent).replace(/code>/g, "pre>");

		$("#loading").hide();
		$( "#codePreview pre" ).append(output);

		$("#learnMoreButton").show();

		
	    }).
	    error(function(data, status, headers, config) {
		console.log(data);
	    });
	
    };

});
 
