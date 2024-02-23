public class Example {
  
  public void defaultCredentialsExample() {
    AWSCredentialsProvider credentialsProvider = client.createDefaultCredentialsProvider();
    SQSExtendedClient client = new SQSExtendedClient();

    String queueUrl = client.createQueue(credentialsProvider);
    client.sendMessageThroughS3(credentialsProvider, queueUrl, "A very long message...");
  }

  class MyCredentialsProvider implements AWSCredentialsProvider {

    @Override
    public AWSCredentials getCredentials() {
      return someOtherSystem.fetchCredentials();
    }
  }

  public void customCredentialsExample() {
    AWSCredentialsProvider credentialsProvider = new MyCredentialsProvider();
    SQSExtendedClient client = new SQSExtendedClient();
    
    String queueUrl = client.createQueue(credentialsProvider);
    client.sendMessageThroughS3(credentialsProvider, queueUrl, "A very long message...");
  }

}
