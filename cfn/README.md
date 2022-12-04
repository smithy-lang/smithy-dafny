#### Testing CA
The CFN stacks here SHOULD allow the IAM role Tools Development to
access the Code Artifact Resources created.

But not directly.
Instead, the stacks allow the Dev role to ASSUME 
the created IAM Roles.

Here is a little bash that can do that.
In addition to the `isengardcli`, it relies on `jq` and the `aws-cli`, 
both of which are on Homebrew and should be available for Windows or Linux.
Don't forget to set the opening variables.
```shell
export AWS_REGION="us-west-2"
export ACCOUNT_ID=827585335069 # 827585335069 is Tony Knapp's Dev account
export ASSUME_ROLE="arn:aws:iam::${ACCOUNT_ID}:role/Polymorph-CA-SourceRole-${AWS_REGION}"
# the alternative is
# arn:aws:iam::${ACCOUNT_ID}:role/Polymorph-CA-PullRole-${AWS_REGION}
eval `isengardcli credentials --region "$AWS_REGION" --role ToolsDevelopment --shell sh "$ACCOUNT_ID"`

STS_RESPONSE=`aws sts assume-role \
  --role-session-name "test" \
  --role-arn "$ASSUME_ROLE" \
  --output json`
# Now, we use `jq` to parse the result
export AWS_ACCESS_KEY_ID=`echo "$STS_RESPONSE" | jq -r .Credentials.AccessKeyId`
export AWS_SECRET_ACCESS_KEY=`echo "$STS_RESPONSE" | jq -r .Credentials.SecretAccessKey`
export AWS_SESSION_TOKEN=`echo "$STS_RESPONSE" | jq -r .Credentials.SessionToken`
# and now we can fetch the CA token
export CODEARTIFACT_AUTH_TOKEN=`aws codeartifact get-authorization-token \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --query authorizationToken \
  --output text`
# and the repo urls
export CODEARTIFACT_URL_CONVERSION=`aws codeartifact get-repository-endpoint \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --repository DafnyJavaConversion \
  --format maven | jq -r .repositoryEndpoint`
export CODEARTIFACT_URL_SMITHY=`aws codeartifact get-repository-endpoint \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --repository SmithyPolymorph \
  --format maven | jq -r .repositoryEndpoint`
```

More instructions can be read 
[in the CA User Guide](https://docs.aws.amazon.com/codeartifact/latest/ug/maven-gradle.html).

If you want to check how the results of the above,
try `env | grep CODE`, or `env | grep AWS`.
Those should print the intermediate and final env variables.

Groovy. 
I have tried to hack the bloody Gradle script to conditionally publish.
Let's see if that works.
Run the above, and then `gradle publish`.

### Reset
Shell command to reset the environment:
```shell
unset STS_RESPONSE AWS_ACCESS_KEY_ID AWS_SECRET_ACCESS_KEY \
  AWS_SESSION_TOKEN CODEARTIFACT_AUTH_TOKEN \
  CODEARTIFACT_URL_CONVERSION CODEARTIFACT_URL_SMITHY
```

### Test Pulling
You can test the Pull permissions by running the above command followed by:
```shell
aws codeartifact list-package-version-assets \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --repository DafnyJavaConversion \
  --format maven \
  --package conversion \
  --namespace software.amazon.dafny \
  --package-version 1.0-SNAPSHOT
```

Update the Asset parameter below to test pulling a Jar.
```shell
aws codeartifact get-package-version-asset \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --repository DafnyJavaConversion \
  --format maven \
  --namespace software.amazon.dafny \
  --package conversion \
  --package-version "1.0-SNAPSHOT" \
  --asset "conversion-1.0-20221204.020926-1.jar" \
  a.jar
```
