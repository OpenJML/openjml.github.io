# -*- mode: ruby -*-
# vi: set ft=ruby :

Vagrant.configure(2) do |config|
  config.vm.box = "hashicorp/precise32"
  config.vm.network :forwarded_port, host: 4000, guest: 4000
  config.vm.provision "shell", inline: <<-SHELL
     sudo apt-get update
     sudo apt-get -y install build-essential
     sudo apt-get -y install ruby1.9.1
     sudo apt-get -y install ruby1.9.1-dev
     sudo gem install --no-ri --no-rdoc jekyll
     sudo apt-get -y install nodejs 
     sudo apt-get -y install python-pip
     sudo pip install Pygments
     sudo apt-get -y install rubygems
     sudo apt-get -y install ruby-bundler
     bundle install
  SHELL
end
