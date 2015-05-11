# To Edit OpenJML.org

OpenJML.org uses a static site generator called Jekyll. Setting this up is quite a pain so we've made things easy for you using Vagrant. To work with OpenJML.org:

1. Install Vagrant. You'll likely want to get it from http://vagrantup.com
2. Execute the following command to start your vagrant instance:

```shell
# vagrant up
```

3. Execute the following command to log into your vagrant instance:

```shell
# vagrant ssh
```

4. Lastly, start Jekyll up.


```shell
# cd /vagrant
# jekyll serve -H 0.0.0.0 -w --force_polling
```

If all that went well, you should be able to see the OpenJML.org site at http://127.0.0.1:4000


# Questions?

Please email me at jls@cs.ucf.edu. I'll be happy to help. 
