## Fetching CA Credentials

The CFN stacks here SHOULD allow the IAM role Tools Development to
access the Code Artifact Resources created.

But not directly.
Instead, the stacks allow the Dev role to ASSUME
the created IAM Roles.

Here is a little bash that can do that.
In addition to the `isengardcli`, it relies on `jq` and the `aws-cli`,
both of which are on Homebrew and should be available for Windows or Linux.
Don't forget to set the opening variables.

#### Script

```shell
export AWS_REGION="us-west-2"
export ACCOUNT_ID=370957321024 # 370957321024 is the Ops CI Account
export ASSUME_ROLE="arn:aws:iam::${ACCOUNT_ID}:role/Polymorph-CA-PullRole-${AWS_REGION}"
# the alternative is
# arn:aws:iam::${ACCOUNT_ID}:role/Polymorph-CA-SourceRole-${AWS_REGION}
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
export CODEARTIFACT_URL_JAVA_CONVERSION=`aws codeartifact get-repository-endpoint \
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

#### Details

More instructions can be read
[in the CA User Guide](https://docs.aws.amazon.com/codeartifact/latest/ug/maven-gradle.html).

If you want to check how the results of the above,
try `env | grep CODE`, or `env | grep AWS`.
Those should print the intermediate and final env variables.

### Reset

Shell command to reset the environment:

```shell
unset STS_RESPONSE AWS_ACCESS_KEY_ID AWS_SECRET_ACCESS_KEY \
  AWS_SESSION_TOKEN CODEARTIFACT_AUTH_TOKEN \
  CODEARTIFACT_URL_JAVA_CONVERSION CODEARTIFACT_URL_SMITHY
```

### Publish `DafnyJavaConversion` or `SmithyPolymorph` to CA

From the same directory as the project,
Run the [script above](#script), and then `gradle publish`.

### Test Pulling

To test the Pull permissions or
fetch a Jar from CA for local use,
you need to determine the Asset Name for the Jar,
and then fetch that Jar via the Asset Name.

1. Fetch `CODEARTIFACT_AUTH_TOKEN` and CA Endpoint URL with [script above](#script)
2. Run the following to retrieve a list of asset names,  
   and manually copy the name

```shell
CA_REPOSITORY="DafnyJavaConversion"
CA_PACKAGE="conversion"
CA_NAMESPACE="software.amazon.dafny"
CA_VERSION="1.0-SNAPSHOT"
aws codeartifact list-package-version-assets \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --repository "$CA_REPOSITORY" \
  --format maven \
  --package "$CA_PACKAGE" \
  --namespace "$CA_NAMESPACE" \
  --package-version "$CA_VERSION" | jq -r .assets
```

3. Run the following to retrieve the Jar,  
   replacing `CA_ASSET_NAME` with the value from (2.)

```shell
CA_ASSET_NAME="conversion-1.0-20221214.000034-1.jar"
aws codeartifact get-package-version-asset \
  --domain github-polymorph \
  --domain-owner "$ACCOUNT_ID" \
  --repository "$CA_REPOSITORY" \
  --format maven \
  --package "$CA_PACKAGE" \
  --namespace "$CA_NAMESPACE" \
  --package-version "$CA_VERSION" \
  --asset "$CA_ASSET_NAME" \
  $CA_ASSET_NAME
```

4. (Optional) Install the Jar to Maven local via:

```shell
mvn -B -ntp install:install-file \
-Dfile="$CA_ASSET_NAME" \
-DgroupId="$CA_NAMESPACE" \
-DartifactId="$CA_PACKAGE" \
-Dversion="$CA_VERSION" \
-DgeneratePom=true \
-Dpackaging=jar
```

### Push an arbitrary Java package to CA

Here, I pushed the DafnyRuntime Jar to the Dafny->Java conversion repository,
but you could customize the following to push any Jar.

1. Follow AWS Docs [instructions to configure `~/.m2/settings.xml`](https://docs.aws.amazon.com/codeartifact/latest/ug/maven-mvn.html#publishing-third-party-artifacts).
2. Fetch `CODEARTIFACT_AUTH_TOKEN` and CA Endpoint URL with [script above](#script)
3. Customize and run

```shell
mvn deploy:deploy-file \
-DgroupId=dafny.lang \
-DartifactId=DafnyRuntime \
-Dversion=3.10.0 \
-Dfile=./DafnyRuntime.jar \
-Dpackaging=jar \
-DrepositoryId=codeartifact \
-Durl="$CODEARTIFACT_URL_JAVA_CONVERSION"
```
